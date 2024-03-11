def wedge(graph: dict[int, list[int]], s, t, w):
	atoms = []
	for source in graph:
		for target, weight in graph[source]:
			atoms.append(z3.And([s == source, t == target, w == weight])) 
			atoms.append(z3.And([s == target, t == source, w == weight]))
	bf = z3.Or(atoms)
	return bf
