def distinct_vs(vertices):
	n = len(vertices)
	atoms = []
	for i in range(n - 1):
		for j in range(i + 1, n):
			atoms.append(vertices[i] != vertices[j])
	bf = z3.And(atoms)
	return bf
