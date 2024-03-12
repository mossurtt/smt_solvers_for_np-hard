import z3 

def proper_numbers(vertices):
    n = len(vertices)
    atoms = []
    for i in range(n):
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

def dir_edge(digraph: dict[int, list[int]], s, t):
    atoms = []
    for source in digraph:
        for target in digraph[source]:
            atoms.append(z3.And([s == source, t == target]))
    bf = z3.Or(atoms)
    return bf

def edge(graph: dict[int, list[int]], s, t):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.And([s == source, t == target])) 
            atoms.append(z3.And([s == target, t == source]))
    bf = z3.Or(atoms)
    return bf

def wedge(graph: dict[int, list[int]], s, t, w):
    atoms = []
    for source in graph:
        for target, weight in graph[source]:
            atoms.append(z3.And([s == source, t == target, w == weight])) 
            atoms.append(z3.And([s == target, t == source, w == weight]))
    bf = z3.Or(atoms)
    return bf
