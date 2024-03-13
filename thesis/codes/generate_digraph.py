def generate_digraph():
    for i in range(4, 25, 2):
            g1 = ig.Graph.Barabasi(i, i // 2, directed=True)
            g1.write_edgelist(f'barabasi/barabasi_{i}.txt')

            g2 = ig.Graph.Erdos_Renyi(n=i, p=0.98, directed=True)
            g2.write_edgelist(f'erdos_renyi/erdos_renyi_{i}.txt')
