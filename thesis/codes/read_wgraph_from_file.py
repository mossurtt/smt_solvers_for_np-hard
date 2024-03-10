def read_wgraph_from_file(filename):
	with open(filename, 'r') as file:
	lines = file.readlines()
	
	wgraph = {}
	for line in lines:
		source, target, weight = [int(x) for x in line.strip().split()]
		if source not in wgraph:
			wgraph[source] = []
		if target not in wgraph:
			wgraph[target] = []
		wgraph[source].append((target, weight))
		wgraph[target].append((source, weight))
	
	return wgraph
