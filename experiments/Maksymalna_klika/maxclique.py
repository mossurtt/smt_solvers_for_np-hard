import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxclique.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)

    for k in range(2, n + 1):
        result, model = check_clique(graph, k)
        if result != z3.sat:
            break

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
        graph[target].append(source)
    print(graph)
        
    return graph

def check_clique(graph: dict[int, list[int]], k):

    n = len(graph)

    vertices = z3.IntVector("v", n)
    solver = z3.Solver()

    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))
        
    edges = []
    for i in range(k):
        for j in range(i + 1, k):
            edges.append(edge(graph, vertices[i], vertices[j]))
    solver.add(z3.And(edges))

    result = solver.check() 
    if result == z3.sat:
        print('Znaleziono klike o rozmiarze', k)
        model = solver.model()
        clique = [model[vertices[i]].as_long() for i in range(k)]
        print(clique)
    else:
        print('Nie znaleziono kliki o rozmiarze', k)
        model = None

    smt2_representation = solver.to_smt2()
    file_name = f'maxclique_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    return (result, model)
    
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

    
    
