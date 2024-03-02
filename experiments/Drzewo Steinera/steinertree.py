from z3 import *

def minimum_steiner_tree(adjacency_list, marked_vertices):
    # Extract vertices from adjacency list
    vertices = list(adjacency_list.keys())

    # Define variables
    edges = [(i, j) for i in adjacency_list for j in adjacency_list[i] if i < j and j in adjacency_list[i]]
    edge_vars = {edge: Bool(f'e_{edge[0]}_{edge[1]}') for edge in edges}

    # Initialize bounds for binary search
    lo = min(adjacency_list[edge[0]][edge[1]] for edge in edges)
    hi = sum(adjacency_list[edge[0]][edge[1]] for edge in edges)

    best_steiner_tree_edges = None
    best_weight = float('inf')

    # Binary search for the minimum weight
    while lo <= hi:
        mid = (lo + hi) // 2

        # Define Z3 solver
        solver = Solver()

        # Define variables for marked vertices
        marked_vars = {vertex: Bool(f'm_{vertex}') for vertex in vertices}

        # Define constraints for marked vertices
        for vertex in vertices:
            if vertex in marked_vertices:
                solver.add(marked_vars[vertex])
            else:
                solver.add(Not(marked_vars[vertex]))

        # Define constraints for edge variables
        for edge in edges:
            connected_vertices = Or(marked_vars[edge[0]], marked_vars[edge[1]])
            solver.add(Implies(edge_vars[edge], connected_vertices))
            solver.add(Implies(connected_vertices, edge_vars[edge]))  # Ensure connectivity

        # Add constraint for maximum weight
        solver.add(Sum([If(edge_vars[edge], adjacency_list[edge[0]][edge[1]], 0) for edge in edges]) <= mid)

        # Check if solution exists
        if solver.check() == sat:
            model = solver.model()
            steiner_tree_edges = [edge for edge in edges if model[edge_vars[edge]]]
            steiner_tree_weight = sum(adjacency_list[edge[0]][edge[1]] for edge in steiner_tree_edges)

            if steiner_tree_weight < best_weight:
                best_steiner_tree_edges = steiner_tree_edges
                best_weight = steiner_tree_weight

            hi = mid - 1
        else:
            lo = mid + 1

    return best_steiner_tree_edges

# Example usage
adjacency_list = {
    0: {1: 2, 2: 3},
    1: {0: 2, 2: 4, 3: 5},
    2: {0: 3, 1: 4, 3: 6},
    3: {1: 5, 2: 6}
}
marked_vertices = [0, 2, 3]

steiner_tree_edges = minimum_steiner_tree(adjacency_list, marked_vertices)
if steiner_tree_edges:
    print("Minimum Weight Steiner Tree Edges:", steiner_tree_edges)
else:
    print("No Steiner Tree found for the given marked vertices.")
