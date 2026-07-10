import json

# JSON data
data = {
    "Test": "protocols",
    "feynman": {
        "Circuits": [
            {
                "name": "sd",
                "sim_time": 0.00047289999999999995,
                "check_time": 0.0002223,
                "total_time": 0.0006952,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "teleport",
                "sim_time": 0.0002632,
                "check_time": 0.0003505,
                "total_time": 0.0006137,
                "expansions": 0,
                "qwidth": 3,
                "success": True
            },
            {
                "name": "t_gate_teleportation",
                "sim_time": 1.6899999999999997e-05,
                "check_time": 0.00033299999999999996,
                "total_time": 0.00034989999999999994,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "distributeBell",
                "sim_time": 1.36e-05,
                "check_time": 0.00048279999999999997,
                "total_time": 0.0004963999999999999,
                "expansions": 0,
                "qwidth": 4,
                "success": True
            },
            {
                "name": "bell_state_prep",
                "sim_time": 3.8100000000000005e-05,
                "check_time": 0.0002779,
                "total_time": 0.000316,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "qftn",
                "sim_time": 9.33e-05,
                "check_time": 0.029752100000000004,
                "total_time": 0.029845400000000005,
                "expansions": 0,
                "qwidth": 10,
                "success": True
            }
        ]
    },
    "no-comp": {
        "Circuits": [
            {
                "name": "sd",
                "sim_time": 0.0004649,
                "check_time": 0.00022329999999999998,
                "total_time": 0.0006882,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "teleport",
                "sim_time": 0.0002647,
                "check_time": 0.0003618,
                "total_time": 0.0006265,
                "expansions": 0,
                "qwidth": 3,
                "success": True
            },
            {
                "name": "t_gate_teleportation",
                "sim_time": 1.69e-05,
                "check_time": 0.0003367,
                "total_time": 0.0003536,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "distributeBell",
                "sim_time": 0.00029180000000000005,
                "check_time": 0.0002425,
                "total_time": 0.0005343,
                "expansions": 0,
                "qwidth": 4,
                "success": True
            },
            {
                "name": "bell_state_prep",
                "sim_time": 3.95e-05,
                "check_time": 0.00028869999999999997,
                "total_time": 0.00032819999999999995,
                "expansions": 0,
                "qwidth": 2,
                "success": True
            },
            {
                "name": "qftn",
                "sim_time": 9.02e-05,
                "check_time": 0.0297014,
                "total_time": 0.029791599999999998,
                "expansions": 0,
                "qwidth": 10,
                "success": True
            }
        ]
    }
}

# Create dictionaries for easy lookup
feynman_circuits = {circuit['name']: circuit for circuit in data['feynman']['Circuits']}
nocomp_circuits = {circuit['name']: circuit for circuit in data['no-comp']['Circuits']}

# Generate LaTeX rows
print("LaTeX table rows:")
print()

for circuit_name in feynman_circuits.keys():
    feynman = feynman_circuits[circuit_name]
    nocomp = nocomp_circuits[circuit_name]
    
    # Extract values (convert seconds to milliseconds)
    name = feynman['name']
    qwidth = feynman['qwidth']
    expansions = feynman['expansions']
    feynman_sim = feynman['sim_time'] * 1000  # Convert to ms
    feynman_check = feynman['check_time'] * 1000  # Convert to ms
    feynman_total = feynman['total_time'] * 1000  # Convert to ms
    nocomp_total = nocomp['total_time'] * 1000  # Convert to ms
    
    # Format the LaTeX row
    row = f"         & {name} & {qwidth} & {expansions} & {feynman_sim:.1f} & {feynman_check:.1f} & {feynman_total:.1f} & {nocomp_total:.1f} & - & - \\\\ \\cline{{2-10}}"
    print(row)