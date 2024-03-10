def check_coloring(graph, k):
	vertices = list(graph.keys())
	n = len(vertices)
	
	vertex_color = z3.IntVector('v', n)
	
	solver = z3.Solver()
	
	for i in range(n):
		solver.add(vertex_color[i] >= 1)
		solver.add(vertex_color[i] <= k)
	
	for i in range(n):
		for neighbor in graph[vertices[i]]:
			solver.add(vertex_color[i] != vertex_color[vertices[neighbor]])
	
	smt2_representation = solver.to_smt2()
	file_name = f'graphcoloring_state.smt2'
	with open(file_name, 'w') as file:
		file.write("(set-logic ALL)\n")
		file.write(smt2_representation)  
	file.close()
	
	result = solver.check()
	
	if result == z3.sat:
		print(result)
		model = solver.model()
		print(model)
		draw_graph(graph, vertex_color, model)
	else:
		print(result)
		model = None
	
	return result, model
