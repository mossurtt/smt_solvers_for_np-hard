def edge(graph: dict[int, list[int]], s, t):
	atoms = []
	for source in graph:
		for target in graph[source]:
			atoms.append(z3.And([s == source, t == target])) 
			atoms.append(z3.And([s == target, t == source]))
	bf = z3.Or(atoms)
	return bf
