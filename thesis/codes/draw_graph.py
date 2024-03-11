def draw_graph(graph, vertex_color, model):
    G = nx.Graph()
    for vertex, neighbors in graph.items():
        G.add_node(vertex)
        for neighbor in neighbors:
            G.add_edge(vertex, neighbor)

    colors = [model.evaluate(vertex_color[v]).as_long() for v in graph]

    nx.draw(G, with_labels=True, node_color=colors, cmap = 'tab10')
    plt.show()
