import sys
import z3

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxclique.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    maxclique = check_maxclique(graph)
    if maxclique:
        print("Maximal clique:", maxclique)
        print("Size:", len(maxclique))
    else:
        print("Graph doesn't contain a clique.")

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors
    return graph

def check_maxclique(graph):
    n = len(graph)
    
    vertices =  z3.IntVector('v', n)
    
    solver = z3.Solver()
    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))
    max_size = 0
    left = 0
    right = n
    
    while left <= right:
        mid = (left + right) // 2
        solver.reset()
        solver.add(z3.Sum([z3.If(v > 1, 1, 0) for v in vertices]) <= mid)
        
        for i in range(n):
            for j in range(i + 1, n):
                if j not in graph[i]: 
                    solver.add(z3.Implies(z3.And(vertices[i] > 0, vertices[j] > 0), z3.Or(vertices[i] <= 0, vertices[j] <= 0)))
        
        if solver.check() == z3.sat:
            max_size = mid
            left = mid + 1
        else:
            right = mid - 1
    
    
    smt2_representation = solver.to_smt2()
    file_name = f'maxclique_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()
    print(solver.model())
    return [i for i in range(n) if solver.model()[vertices[i]].as_long() > 0]

def proper_numbers(vertices):
    n = len(vertices)
    atoms = []
    for i in range(n - 1):
        atoms.append(z3.And(vertices[i] >= 0, vertices[i] < n))
    bf = z3.And(atoms)
    return bf

def distinct_vs(vertices):
    n = len(vertices)
    atoms = []
    for i in range(n - 1):
        for j in range(i + 1, n):
            atoms.append(vertices[i] != vertices[j])
    bf = z3.And(atoms)
    return bf

if __name__ == "__main__":
    main()
