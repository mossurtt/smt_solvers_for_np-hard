import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxindset.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)

    maxindset = check_maxindset(graph)
    if maxindset:
        print('Maximal independent set:', maxindset)
        print('Size:', len(maxindset))
    else:
        print('unsat')

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

def check_maxindset(graph: dict[int, list[int]]):

    n = len(graph)
    k = 1

    for k in range(2, n + 1):
        vertices = z3.IntVector("v", n)
        solver = z3.Solver()

        solver.add(proper_numbers(vertices))
        solver.add(distinct_vs(vertices))
            
        no_edges = []
        for i in range(k):
            for j in range(i + 1, k):
                    no_edges.append(z3.Not(edge(graph, vertices[i], vertices[j])))
        solver.add(z3.And(no_edges))

        result = solver.check() 
        if result == z3.sat:
            model = solver.model()
            maxindset = [model[vertices[i]].as_long() for i in range(k)]
        else:
            break

    smt2_representation = solver.to_smt2()
    file_name = f'maxindset_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    return maxindset
    
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

    
    
