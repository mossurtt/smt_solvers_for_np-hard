import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxindset.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    mis = check_maxindset(graph)
    if mis:
        print("Maximum inependent set:", mis)
    else:
        print("Graph doesn't contain a MIS.")

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors
    return graph

def check_maxindset(graph):
    n = len(graph)
    
    vertices = z3.BoolVector('v', n)
    
    solver = z3.Solver()
        
    max_size = 0
    left = 0
    right = n
    
    while left <= right:
        mid = (left + right) // 2
        solver.reset()
        solver.add(z3.Sum([z3.If(vertices[i], 1, 0) for i in range(n)]) <= mid)

        for i in range(n):
            for j in range(i + 1, n):
                if j in graph[i]: 
                    solver.add(z3.Implies(z3.And(vertices[i], vertices[j]), z3.Not(vertices[i])))
                    solver.add(z3.Implies(z3.And(vertices[i], vertices[j]), z3.Not(vertices[j])))

        if solver.check() == z3.sat:
            max_size = mid
            left = mid + 1
        else:
            right = mid - 1

    smt2_representation = solver.to_smt2()
    file_name = f'maxindset_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()
    
    return [i for i in range(n) if solver.model()[vertices[i]]]

if __name__ == "__main__":
    main()
