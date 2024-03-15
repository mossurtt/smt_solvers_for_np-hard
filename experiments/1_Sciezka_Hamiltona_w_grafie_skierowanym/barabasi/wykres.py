import os
import re 
import numpy as np
import matplotlib.pyplot as plt
from scipy.interpolate import interp1d

def parse_log_file(log_file):
    with open(log_file, 'r') as file:
        lines = file.readlines()
    
    n = int(log_file.split("/")[-1].split("-")[0])
    
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

    solver_colors = {'z3': 'green', 'yices': 'blue', 'cvc5': 'orange'}

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

    max_memory = max([entry[2] for data in solvers.values() for entry in data])
    min_memory = min([entry[2] for data in solvers.values() for entry in data])

    memory_range = max_memory - min_memory
    
    for solver, data in sorted_data.items():
        ns = [entry[0] for entry in data]
        times = [entry[1] for entry in data]
        memories = [entry[2] for entry in data]

        color = solver_colors.get(solver, 'black')
        
        ax1.plot(ns, times, linestyle='-', label=solver, linewidth=3, color=color)

        ax2.fill_between(ns, memories, alpha=0.2, color=color)

    ax1.set_xticks(range(4, 25, 2))

    memory_ticks = np.linspace(min_memory, max_memory, 10)
    memory_ticks_labels = [str(int(round(x, -3))) for x in memory_ticks]
    ax2.set_yticks(memory_ticks)
    ax2.set_yticklabels(memory_ticks_labels)

    ax1.set_xlabel('Rozmiar grafu (n)')
    ax1.set_ylabel('Czas (s)')
    ax2.set_ylabel('Pamięć (kB)')
    ax1.set_title('Wyniki dla HamPath (Barabasi)')
    ax1.legend()
    plt.savefig('1-barabasi-plot.png') 
    plt.show()

log_dir = 'logs'
plot_log_files(log_dir)