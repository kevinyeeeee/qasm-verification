#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
import json
from os.path import splitext, join
import subprocess
import sys
import time
import matplotlib
import matplotlib as mpl
mpl.use('pgf')
import numpy as np
import matplotlib.pyplot as plt
import re

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
TIMEOUT_TIME = 600

REPETITION_COUNT = 10

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

def gather_datum(prog_call, path, base, additional_flags):
    start = time.time()
    flags = BASE_FLAGS + additional_flags
    print(prog_call + BASE_FLAGS + flags + [join(path, base + TEST_EXT)])
    proc = EasyProcess(prog_call + BASE_FLAGS + flags + [join(path, base + TEST_EXT)])
    try:
        process_output = proc.call(timeout=TIMEOUT_TIME+5)
    finally:
        proc.stop()
    end = time.time()
    return ((end - start), proc.stdout,proc.stderr)

def parse_output(datum):
    # Regular expression pattern to capture the name and the 4 metrics
    pattern = r"Verifying\s+(.*?)\.\.\.\s*\n\s*Completed\s*\((.*?)\/(.*?)\/(.*?)\/(.*?)\/(.*?)\)"

    # Find all occurrences in the text
    matches = re.findall(pattern, datum)

    # Build the structured dictionary list
    parsed_list = []
    for match in matches:
        parsed_list.append({
            "name": match[0],
            "sim_time": float(match[1]),
            "check_time": float(match[2]),
            "expansions": int(match[3]),
            "qwidth": int(match[4]),
            "success": True if match[5] == "true" else False
        })

    return parsed_list

def feynman_run(path,base,flags):
    data = {"Runs":[]}
    for i in range(REPETITION_COUNT):
        run = {}
        (time,datum,err) = gather_datum(["cabal","run","tcqasm"], path, base, flags)
        error = False

        if time >= TIMEOUT_TIME:
            print("timed out")
            run["Result"] = "Timeout"
            run["Output"] = datum
            error = True
        elif datum == "":
            print("memoried out")
            run["Result"] = "Memout"
            run["Output"] = datum
            error = True

        if error:
            run["Circuits"] = []
            data["Runs"] = data["Runs"] + [run]
            break

        run["Result"] = "Success"
        run["Output"] = datum
        run["Circuits"] = parse_output(datum)
        data["Runs"] = data["Runs"] + [run]
    data["Circuits"] = []
    all_circs = [circ for run in data["Runs"] for circ in run["Circuits"]]
    for cname in set([circ["name"] for circ in all_circs]):
        circ_data = {}
        relevant_circs = [circ for circ in all_circs if circ["name"] == cname]
        circ_data["name"] = cname
        circ_data["sim_time"] = average([circ["sim_time"] for circ in relevant_circs])
        circ_data["check_time"] = average([circ["check_time"] for circ in relevant_circs])
        circ_data["total_time"] = circ_data["sim_time"] + circ_data["check_time"]
        circ_data["expansions"] = relevant_circs[0]["expansions"]
        circ_data["qwidth"] = relevant_circs[0]["qwidth"]
        circ_data["success"] = relevant_circs[0]["success"]
        data["Circuits"] = data["Circuits"] + [circ_data]
    return data

def gather_data(path, base, name):
    current_data = {"Test":name}
    current_data["feynman"] = feynman_run(path,base,[])
    current_data["no-comp"] = feynman_run(path,base,["no-comp"])

    """def gather_col(flags, run_combiner, col_names, timeout_time, repetition_count, compare):
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
                current_data[col_name] = data"""

    """def ctime_combiner(run_data_transpose):
        data_indices = range(1,len(run_data_transpose))
        cols = [[float(x) for x in run_data_transpose[i]] for i in data_indices]
        averages = [average(col) for col in cols]
        return averages"""

    #gather_col([],ctime_combiner,["SimulationTime","CheckingTime","ExpansionCount","ComputationTime"],TIMEOUT_TIME,REPETITION_COUNT,False)

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

def print_json_data(data,name):
    #clean_full_data(data)
    ensure_dir("generated-data/")
    with open("generated-data/" + name, "w") as jsonfile:
        json.dump(data, jsonfile, indent=4)

def print_data(data,name):
    clean_full_data(data)
    ensure_dir("generated-data/")
    with open("generated-data/" + name, "w") as csvfile:
        datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
        datawriter.writeheader()
        datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <benchmark_dir>".format(args[0]))

def load_json_data(name):
    try:
        with open("generated-data/" + name, "r") as jsonfile:
            return json.load(jsonfile)
    except:
        return []

def load_data(name):
    try:
        with open("generated-data/" + name, "r") as csvfile:
            datareader = csv.DictReader(csvfile)
            return [row for row in datareader]
    except:
        return []
    
def makejson(benchmark_path,data_file):
        data = load_json_data(data_file)
        print("existing data")
        print(data)
        if os.path.exists(benchmark_path) and os.path.isdir(benchmark_path):
            rootlength = len(benchmark_path)
            for path, base in find_tests(benchmark_path):
                assert(join(path, base)[rootlength-1] == '/')
                test_name = join(path, base).replace("_","-")[rootlength:]
                print(test_name)
                if (not (any(str(row["Test"]) == str(test_name) for row in data))):
                    current_data = gather_data(path, base, test_name)
                    data.append(current_data)
                    print_json_data(data,data_file)
                else:
                    print("data already retrieved")
            sort_data(data)
            print_json_data(data,data_file)
        else:
            print(args)
            print_usage(args)

def makecuccarograph():
    qftdata = load_data("cuccaro.csv")
    fig, ax = plt.subplots()

    def create_line_plot(data, outputname):
        xs = [x for x in project_column_from_csv(data, "Test")]
        ys = [y for y in project_column_from_csv(data, "ComputationTime")]
        xys = [(int(x),float(y)) for x, y in zip(xs, ys) if can_be_float(y)]
        xys = sorted(xys, key=lambda x: x[0])
        xs,ys = zip(*xys)
        print(xs)
        print(ys)
        ax.plot(xs,ys,marker='.',label=outputname)

    create_line_plot(qftdata,"cuccaro")

    ax.set_ylabel('Time (s)')
    ax.set_xlabel('Input Size')
    xpos = 13
    ax.axvline(x=xpos, color='red', linestyle='--', linewidth=2)
    ax.text(xpos, ax.get_ylim()[1]+215, "timeout", ha='center', va='top', color='red')

    plt.xlim(0,15)
    plt.yticks(np.arange(0, 300.1, 50))

    plt.title("Cuccaro")

    fig = plt.figure(2,tight_layout=True)
    fig.set_figheight(2)
    fig.set_figwidth(3)

    fig.savefig("generated-data/cuccaro.eps", bbox_inches='tight')

def makemultgraph():
    qftdata = load_data("mult.csv")
    fig, ax = plt.subplots()

    def create_line_plot(data, outputname):
        xs = [x for x in project_column_from_csv(data, "Test")]
        ys = [y for y in project_column_from_csv(data, "ComputationTime")]
        xys = [(int(x),float(y)) for x, y in zip(xs, ys) if can_be_float(y)]
        xys = sorted(xys, key=lambda x: x[0])
        xs,ys = zip(*xys)
        print(xs)
        print(ys)
        ax.plot(xs,ys,marker='.',label=outputname)

    create_line_plot(qftdata,"mult")

    ax.set_ylabel('Time (s)')
    ax.set_xlabel('Input Size')
    xpos = 7
    ax.axvline(x=xpos, color='red', linestyle='--', linewidth=2)
    ax.text(xpos, ax.get_ylim()[1]+290, "timeout", ha='center', va='top', color='red')

    plt.xlim(0,8)
    plt.yticks(np.arange(0, 300.1, 50))

    plt.title("Multiply")

    fig = plt.figure(3,tight_layout=True)
    fig.set_figheight(2)
    fig.set_figwidth(3)

    fig.savefig("generated-data/mult.eps", bbox_inches='tight')

def makeqftgraph():
    qftdata = load_data("qft.csv")
    fig, ax = plt.subplots()

    def create_line_plot(data, outputname):
        xs = [x for x in project_column_from_csv(data, "Test")]
        ys = [y for y in project_column_from_csv(data, "ComputationTime")]
        xys = [(int(x),float(y)) for x, y in zip(xs, ys) if can_be_float(y)]
        xys = sorted(xys, key=lambda x: x[0])
        xs,ys = zip(*xys)
        print(xs)
        print(ys)
        ax.plot(xs,ys,marker='.',label=outputname)

    create_line_plot(qftdata,"QFT")

    ax.set_ylabel('Time (s)')
    ax.set_xlabel('Input Size')
    xpos = 160
    ax.axvline(x=xpos, color='red', linestyle='--', linewidth=2)
    ax.text(xpos, ax.get_ylim()[1]+5, "timeout", ha='center', va='bottom', color='red')

    plt.xlim(0,200)
    plt.yticks(np.arange(0, 300.1, 50))

    plt.title("QFT")

    fig = plt.figure(1,tight_layout=True)
    fig.set_figheight(2)
    fig.set_figwidth(3)

    fig.savefig("generated-data/qft.eps", bbox_inches='tight')

def main(args):
    if len(args) == 2:
        benchmark_path = args[1]
        #qft_path = args[2]
        #cuccaro_path = args[3]
        #mult_path = args[4]
        makejson(benchmark_path,"data.json")
        #makecsv(qft_path,"qft.csv")
        #makecsv(cuccaro_path,"cuccaro.csv")
        #makecsv(mult_path,"mult.csv")
        #makeqftgraph()
        #makecuccarograph()
        #makemultgraph()
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
