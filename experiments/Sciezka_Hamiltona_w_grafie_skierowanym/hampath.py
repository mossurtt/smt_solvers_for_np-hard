import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 hampath.py <filename>")
        return

    filename = sys.argv[1]
    digraph = read_graph_from_file(filename)
    
    check_hampath(digraph)

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for line in lines:
        source, target = [int(x) for x in line.strip().split()]
        if source not in graph:
            graph[source] = []
        if target not in graph:
            graph[target] = []
        graph[source].append(target)
        
    return graph

def check_hampath(graph: dict[int, list[int]]):

    n = len(graph)
    vertices = z3.IntVector("v", n)

    solver = z3.Solver()

    solver.add(proper_numbers(vertices))

    solver.add(distinct_vs(vertices))

    edges = []
    for i in range(n - 1):
        edges.append(edge(graph, vertices[i], vertices[i + 1]))
    solver.add(z3.And(edges))

    smt2_representation = solver.to_smt2()
    file_name = f'hampath_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        vertex_values = [(idx, model[v].as_long()) for idx, v in enumerate(vertices)]
        sorted_verticess = sorted(vertex_values)
        print("Hamiltonian Path:")
        for idx, value in sorted_verticess[:-1]:
            print(f"v__{value}", end=' -> ')
        print(f"v__{sorted_verticess[-1][1]}")
    else:
        print(result)
    
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

def edge(graph: dict[int, list[int]], s, t):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.And([s == source, t == target]))
    bf = z3.Or(atoms)
    return bf


if __name__ == "__main__":
    main()
