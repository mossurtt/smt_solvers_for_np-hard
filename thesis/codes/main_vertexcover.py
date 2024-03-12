def main():
    if len(sys.argv) != 2:
        print("Usage: python3 vertexcover.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)

    for k in range(n, 0, -1):
        result, model = check_vertexcover(graph, k)
        if result != z3.sat:
            break
