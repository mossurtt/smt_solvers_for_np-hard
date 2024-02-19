import z3  
import networkx as nx 
import matplotlib.pyplot as plt

def main():
    filename = 'petersen_graph.txt'
    petersen_graph = read_graph_from_file(filename)
    
    check_coloring(petersen_graph)

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors

    return graph

def check_coloring(graph):
    vertices = list(graph.keys())
    n = len(graph)

    vertex_color = [z3.Int(f'vertex_color{i}') for i in range(n)]

    solver = z3.Solver()

    for i in range(n):
        solver.add(vertex_color[i] >= 0)
        solver.add(vertex_color[i] < 3)

    for i in range(n):
        for n in graph[vertices[i]]:
            solver.add(vertex_color[i] != vertex_color[vertices.index(n)])

    smt2_representation = solver.to_smt2()
    file_name = f'graphcoloring_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    print(solver.check())
    model = solver.model()
    print(model)

    draw_graph(graph, vertex_color, model)

def draw_graph(graph, vertex_color, model):
    G = nx.Graph()
    for vertex, neighbors in graph.items():
        G.add_node(vertex)
        for neighbor in neighbors:
            G.add_edge(vertex, neighbor)

    z3_coloring = [model.evaluate(vertex_color[vertex]).as_long() for vertex in graph]

    nodes_with_colors = [(node, z3_color) for node, z3_color in zip(graph, z3_coloring)]

    nodes_with_colors.sort(key=lambda x: x[1])

    sorted_nodes, sorted_colors = zip(*nodes_with_colors)

    rgba = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

    colors = [rgba[color] for color in sorted_colors]

    nx.draw(G, nodelist=sorted_nodes, with_labels=True, node_color=colors)
    plt.show()

if __name__ == '__main__':
    main()