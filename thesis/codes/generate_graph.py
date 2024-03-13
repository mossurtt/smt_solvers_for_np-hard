def generate_graph():
    for i in range(4, 25, 2):
        g1 = ig.Graph.Barabasi(i, i // 2)
        g1.write_edgelist(f'barabasi/barabasi_{i}.txt')

        g2 = ig.Graph.Erdos_Renyi(n = i, p = 0.98)
        g2.write_edgelist(f'erdos-renyi/erdos-renyi_{i}.txt')
