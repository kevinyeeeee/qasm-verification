#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time
import matplotlib
import matplotlib as mpl
mpl.use('pgf')
import numpy as np
import matplotlib.pyplot as plt

plt.rc('font', size=10)
plt.rc('legend', fontsize=10)
plt.rcParams['text.usetex'] = True
plt.rcParams['text.latex.preamble'] = r'\usepackage{libertine}'

from math import sqrt

def can_be_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def can_be_int(s):
    try:
        int(s)
        return True
    except ValueError:
        return False
    
def project_column_from_csv(csv_obj, col_name):
    return [r[col_name] for r in csv_obj]

def simple_write_to_file(fname,data):
    text_file = open(fname,"w")
    text_file.write(data)
    text_file.close()

def clean(s):
    s = str(s)
    if can_be_int(s):
        return int(s)
    elif can_be_float(s):
        f = float(s)
        if f.is_integer():
            return int(f)
        else:
            return "{:.2f}".format(float(s))
    elif s == "timeout":
        return "timeout"
    elif s == "error":
        return "error"
    else:
        return s

def stddev(lst):
    mean = float(sum(lst)) / len(lst)
    return sqrt(float(reduce(lambda x, y: x + y, map(lambda x: (x - mean) ** 2, lst))) / len(lst))

def average(lst):
    return sum(lst)/len(lst)


TEST_EXT = '.qasm'
BASE_FLAGS = []
TIMEOUT_TIME = 300

REPETITION_COUNT = 1

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

def transpose(matrix):
    return list(zip(*matrix))

def find_tests(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
    return tests

def find_subs(root):
    dirs = next(os.walk(root))[1]
    groupings=[]
    for direct in dirs:
        files = next(os.walk(join(root,direct)))[2]
        positives = [join(root,direct,f) for f in files if splitext(f)[1] == POS_EXT]
        negatives = [join(root,direct,f) for f in files if splitext(f)[1] == NEG_EXT]
        posndfs = [join(root,direct,f) for f in files if splitext(f)[1] == POSNDF_EXT]
        negndfs = [join(root,direct,f) for f in files if splitext(f)[1] == NEGNDF_EXT]
        groupings.append((direct,positives,posndfs,negatives,negndfs))
    return groupings

def gather_datum(prog_call, path, base, additional_flags, timeout):
    start = time.time()
    flags = additional_flags
    #flags = map(lambda t: t(path,base),additional_flags)
    print(prog_call + BASE_FLAGS + flags + [join(path, base + TEST_EXT)])
    process_output = EasyProcess(prog_call + BASE_FLAGS + flags + [join(path, base + TEST_EXT)]).call(timeout=timeout+5)
    end = time.time()
    return ((end - start), process_output.stdout,process_output.stderr)

def gather_data(path, base, name):
    current_data = {"Test":name}

    def gather_col(flags, run_combiner, col_names, timeout_time, repetition_count, compare):
        run_data = []
        timeout = False
        error = False
        incorrect = False
        memout = False
        iteration = 0
        for iteration in range(repetition_count):
            (time,datum,err) = gather_datum(["cabal","run","tcqasm"], path, base, flags,timeout_time)
            print(time)
            if [line for line in err.splitlines() if not line.startswith("verification success:")] != []:
                print(err)
                error = True
                break
            if time >= TIMEOUT_TIME:
                timeout = True
                break
            if datum == "":
                memout = True
                break
            this_run_data = list(map(lambda d: d.strip(),datum.split(";"))) + [time]
            if iteration == 0 and compare and not check_equal(prog,path,base,this_run_data[0]):
                incorrect = True
            run_data.append(this_run_data)
            iteration = iteration+1
        if error:
            print("error")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        elif timeout:
            print("\\incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        elif memout:
            print("\\incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\na"
        elif incorrect:
            print("incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        else:
            run_data_transpose = transpose(run_data)
            combined_data = run_combiner(run_data_transpose)
            for (col_name,data) in zip(col_names,combined_data):
                current_data[col_name] = data

    def ctime_combiner(run_data_transpose):
        data_indices = range(1,len(run_data_transpose))
        cols = [[float(x) for x in run_data_transpose[i]] for i in data_indices]
        averages = [average(col) for col in cols]
        return averages

    gather_col([],ctime_combiner,["ComputationTime"],TIMEOUT_TIME,REPETITION_COUNT,False)

    return current_data

def extract_test(x):
    return str(x["Test"])

def specsize_compare(x,y):
    return int(x["SpecSize"])-int(y["SpecSize"])

def test_compare(x,y):
    return int(x["Test"])-int(y["Test"])

def sort_data(data):
    data.sort(key=extract_test)#sorted(data,cmp=test_compare)

def clean_full_data(data):
    for row in data:
        for key in row.keys():
            row[key] = clean(row[key])

def print_data(data,name):
    clean_full_data(data)
    ensure_dir("generated-data/")
    with open("generated-data/" + name, "w") as csvfile:
        datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
        datawriter.writeheader()
        datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <benchmark_dir>".format(args[0]))

def load_data(name):
    try:
        with open("generated-data/" + name, "r") as csvfile:
            datareader = csv.DictReader(csvfile)
            return [row for row in datareader]
    except:
        return []
    
def makecsv(benchmark_path,data_file):
        data = load_data(data_file)
        print("existing data")
        print(data)
        if os.path.exists(benchmark_path) and os.path.isdir(benchmark_path):
            rootlength = len(benchmark_path)
            for path, base in find_tests(benchmark_path):
                assert(join(path, base)[rootlength-1] == '/')
                test_name = join(path, base).replace("_","-")[rootlength:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(path, base, test_name)
                    data.append(current_data)
                    print_data(data,data_file)
                else:
                    print("data already retrieved")
            sort_data(data)
            print_data(data,data_file)
        else:
            print(args)
            print_usage(args)

def makegraph():
    qftdata = load_data("qft.csv")
    cuccarodata = load_data("cuccaro.csv")
    fig, ax = plt.subplots()

    def create_line_plot(data, outputname,style,width):
        xs = [x for x in project_column_from_csv(data, "Test")]
        ys = [y for y in project_column_from_csv(data, "ComputationTime")]
        xs = [int(x) for x, y in zip(xs, ys) if can_be_float(y)]
        ys = [float(y) for y in ys if can_be_float(y)]
        print(xs)
        print(ys)
        ax.plot(xs,ys,marker='.',label=outputname)

    #ax.step([0,60],[48.1,48.1],label="Benchmark Count",linestyle=":",
    #        linewidth=1, dashes=(1,1))
    create_line_plot(qftdata,"QFT",1,1)
    create_line_plot(cuccarodata,"Cuccaro",1,1)

    ax.set_ylabel('Time (s)')
    ax.set_xlabel('Input Size')

    #l = ax.legend(bbox_to_anchor=(.4,.9),borderaxespad=0,ncol=1)
    #l = ax.legend(bbox_to_anchor=(1.6,1),borderaxespad=0)
    #plt.setp(l.texts) 

    plt.xlim(0,100)
    plt.yticks(np.arange(0, 300.1, 50))

    fig = plt.figure(1,tight_layout=True)
    fig.set_figheight(2)
    fig.set_figwidth(3)

    fig.savefig("generated-data/times.eps", bbox_inches='tight')

def main(args):
    if len(args) == 4:
        benchmark_path = args[1]
        qft_path = args[2]
        cuccaro_path = args[3]
        makecsv(benchmark_path,"data.csv")
        makecsv(qft_path,"qft.csv")
        makecsv(cuccaro_path,"cuccaro.csv")
        makegraph()
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
