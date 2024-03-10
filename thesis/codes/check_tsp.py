def check_tsp(graph: dict[int, list[int]], k):
	n = len(graph)
	vertices = [z3.Int(f'v_{i}') for i in range(n)]
	
	solver = z3.Solver()
	
	solver.add(proper_numbers(vertices))
	solver.add(distinct_vs(vertices))
	
	edges = []
	total_cost = z3.IntVal(0)
	
	# Ścieżka Hamiltona z dodawaniem kosztów tras (wag krawędzi)
	for i in range(n - 1):
		c = z3.Int(f"w_{vertices[i]}_{vertices[i + 1]}")
		tour_i = wedge(graph, vertices[i], vertices[i + 1], c)
		edges.append(tour_i)
		total_cost += c
	
	# Dodawanie trasy do pierwszego miasta z powrotem oraz jej kosztu
	c_back = z3.Int(f"w_{vertices[n - 1]}_{vertices[0]}")
	tour_back = wedge(graph, vertices[n - 1], vertices[0], c_back)
	edges.append(tour_back)
	total_cost += c_back
	
	solver.add(z3.And(edges))
	
	solver.add(total_cost <= k)
	
	smt2_representation = solver.to_smt2()
	file_name = f'tsp_state.smt2'
	with open(file_name, 'w') as file:
		file.write("(set-logic ALL)\n")
		file.write(smt2_representation)  
	file.close()
	
	result = solver.check()
	if result == z3.sat:
		model = solver.model()
		vertex_values = [(idx, model[v].as_long()) for idx, v in enumerate(vertices)]
		sorted_vertices = sorted(vertex_values)
		print("Tour:")
		for idx, value in sorted_vertices:
			print(f"v__{value}", end=' -> ')
		print(f"v__{sorted_vertices[0][1]}")
		
		# Koszt sumaryczny z modelu
		cost = 0
		for decl in model.decls():
			if decl.name().startswith("w_"):
				value = model[decl].as_long()
				cost += value
		print("Cost:", cost)
	else:
		print(result)
		model = None
		
	return result, model
