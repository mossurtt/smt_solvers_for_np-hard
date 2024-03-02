import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxclique.py <filename>")
        return

    filename = sys.argv[1]
    digraph = read_graph_from_file(filename)

    check_clique(digraph)

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors

    return graph

def check_clique(graph: dict[int, list[int]]):

    n = len(graph)
    vertices = z3.IntVector("v", n)

    solver = z3.Solver()

    solver.add(proper_numbers(vertices))

    solver.add(distinct_vs(vertices))

    k = 0
    lo, hi = 0, n

    while lo <= hi:
        mid = (lo + hi) // 2
        # solver.reset()
        
        edges = []
        for i in range(k):
            for j in range(i + 1, k):
                edges.append(edge(graph, vertices[i], vertices[j]))
        solver.add(z3.And(edges))

        if solver.check() == z3.sat:
            k = mid
            lo = mid + 1
        else:
            hi = mid - 1

    smt2_representation = solver.to_smt2()
    file_name = f'maxclique_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        for i in range(k):
            print(f'Vertex {i}: {model[vertices[i]]}')
    else:
        print(result)
    
def proper_numbers(vertices):
    n = len(vertices)
    atoms = []
    for i in range(n - 1):
        atoms.append(z3.And(vertices[i] >= 0, vertices[i] < n))
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf

def distinct_vs(vertices):
    n = len(vertices)
    atoms = []
    for i in range(n - 1):
        for j in range(i + 1, n):
            atoms.append(vertices[i] != vertices[j])
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf

def edge(graph: dict[int, list[int]], s, t):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.And([s == source, t == target])) 
            atoms.append(z3.And([s == target, t == source]))
    bf = z3.Or(atoms)
    z3.simplify(bf)
    return bf


if __name__ == "__main__":
    main()

    
    
