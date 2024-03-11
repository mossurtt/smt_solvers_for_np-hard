import matplotlib.pyplot as plt 
import pandas as pd 
import os

def main():
    log_dir = 'logs'
    df = plot_log_files(log_dir)

def plot_log_files(log_dir):
    plt.figure(figsize=(10, 6))
    solver_data = {'z3': {'x': [], 'y': []}, 'yices': {'x': [], 'y': []}, 'cvc5': {'x': [], 'y': []}}
    
    for filename in os.listdir(log_dir):
        if filename.endswith('.log') and filename.startswith('hampath'):
            _, n, solver_name = filename.split('-')
            n = int(n)
            solver_name = solver_name[:-4]
            with open(os.path.join(log_dir, filename), 'r') as file:
                for line in file:
                        time, _ = line.strip().split()
                        solver_data[solver_name]['x'].append(n)
                        solver_data[solver_name]['y'].append(float(time))

    for solver_name, data in solver_data.items():
        plt.plot(data['x'], data['y'], label=f'{solver_name}')
    
    plt.ylabel('Time (s)')
    plt.xlabel('n')
    plt.title('Hamiltonian path')
    plt.legend()
    plt.grid(True)
    plt.savefig('hampath_barabasi.png')
    plt.show()


if __name__ == "__main__":
    main()