import os
import re 
import matplotlib.pyplot as plt

def parse_log_file(log_file):
    with open(log_file, 'r') as file:
        lines = file.readlines()
    
    n = int(log_file.split("-")[1])
    
    data = []
    for line in lines:
        if "Command terminated" not in line:
            match = re.match(r'([\d.]+)\s+([\d]+)', line.strip())
            if match:
                time = min(float(match.group(1)), 600)
                memory = int(match.group(2))
                data.append((n, time, memory))
    return data

def plot_log_files(log_dir):
    plt.figure(figsize=(12, 8))

    solvers = {}
    
    markers = [ 'D', 's', 'o'] 

    for filename in os.listdir(log_dir):
        if filename.endswith(".log"):
            solver = filename.split("-")[-1].split(".")[0]
            if solver not in solvers:
                solvers[solver] = []
            
            log_file = os.path.join(log_dir, filename)
            data = parse_log_file(log_file)
            solvers[solver].extend(data)

    sorted_data = {}
    for solver, data in solvers.items():
        sorted_data[solver] = sorted(data, key=lambda x: x[0])

    ax1 = plt.gca()
    ax2 = ax1.twinx()
    
    for i, (solver, data) in enumerate(sorted_data.items()):
        ns = [entry[0] for entry in data]
        times = [entry[1] for entry in data]
        memories = [entry[2] for entry in data]

        marker = markers[i % len(markers)]

        ax1.plot(ns, times, linestyle='-', label=solver, linewidth=4)
        ax1.scatter(ns, times, marker=marker, s=40)
        # ax2.scatter(ns, memories, linestyle='dashed', s=30)

    ax1.set_xticks(range(4, 25, 2))
    
    ax1.set_xlabel('Rozmiar grafu (n)')
    ax1.set_ylabel('Czas (s)')
    # ax2.set_ylabel('Memory (kB)')
    ax1.set_title('Wyniki dla MaxClique (Barabasi)')
    ax1.legend()
    plt.savefig('barabasi-plot.png') 
    plt.show()

log_dir = 'log'
plot_log_files(log_dir)