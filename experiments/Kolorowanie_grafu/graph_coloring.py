import sys
import z3  
from utils.read_input import read_graph_from_file
import networkx as nx 
import matplotlib.pyplot as plt
import matplotlib.cm as cm

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 graph_coloring.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)
    print(graph)
    
    for k in range(1, n + 1):
        result, model = check_coloring(graph, k)
        if result != z3.unsat:
            break


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

def draw_graph(graph, vertex_color, model):
    G = nx.Graph()
    for vertex, neighbors in graph.items():
        G.add_node(vertex)
        for neighbor in neighbors:
            G.add_edge(vertex, neighbor)
    
    if model is not None:
        colors = [model.evaluate(vertex_color[v]).as_long() for v in graph]
        # colormap = cm.tab10.colors[:max(colors) + 1]

        nx.draw(G, with_labels=True, node_color=colors, cmap = 'tab10')
        plt.show()
    else:
        nx.draw(G, with_labels=True)

if __name__ == '__main__':
    main()