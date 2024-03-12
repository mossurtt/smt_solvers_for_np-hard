def main():
    if len(sys.argv) != 2:
        print("Usage: python3 graph_coloring.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)
    
    for k in range(1, n + 1):
        result, model = check_coloring(graph, k)
        if result != z3.unsat:
            break
