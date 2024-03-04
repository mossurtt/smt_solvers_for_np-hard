import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxindset.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)

    print(check_maxindset(graph, 3))

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

def check_maxindset(graph: dict[int, list[int]], k):

    n = len(graph)
    vertices = z3.IntVector("v", n)
    solver = z3.Solver()

    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))
           
    edges = []
    for i in range(k):
        edges.append(edge_covered(graph, vertices[i]))
    solver.add(z3.And(edges))

    smt2_representation = solver.to_smt2()
    file_name = f'vertexcover_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check() 
    if result == z3.sat:
        model = solver.model()
        print(model)
        vertex_cover = [model[vertices[i]].as_long() for i in range(k)]
        return vertex_cover
    else:
        print('Nie znaleziono pokrycia')
        return(result)

    
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

def edge_covered(graph: dict[int, list[int]], v):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.Or([v == source, v == target]))
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf



if __name__ == "__main__":
    main()