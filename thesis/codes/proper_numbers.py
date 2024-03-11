def proper_numbers(vertices):
	n = len(vertices)
	atoms = []
	for i in range(n - 1):
		atoms.append(z3.And(vertices[i] >= 0, vertices[i] < n))
	bf = z3.And(atoms)
	return bf
