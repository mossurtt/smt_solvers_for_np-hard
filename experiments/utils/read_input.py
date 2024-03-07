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
        
    return graph

def read_digraph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    digraph = {}
    for line in lines:
        source, target = [int(x) for x in line.strip().split()]
        if source not in digraph:
            digraph[source] = []
        if target not in digraph:
            digraph[target] = []
        digraph[source].append(target)
        
    return digraph