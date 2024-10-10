from scripts.generate_eqs_list import eqs, format_expr


class EGraph:
    # The e-graph is represented by an array of nodes, consecutively numbered.
    # Since we only have a single operation, the data per node is just the operands and the node class.
    # An array contains data for each node (indexed by node ID), usually it's a list with the IDs of the two
    # children, but in case nodes were merged one of them will refer to the other by replacing its data with
    # the other node's ID. This way we don't need to handle node classes separately.
    # Aliases of nodes are saved here so that the node IDs can be updated in the merge process.

    def __init__(self):
        self.nodes_data = []
        self.node_aliases = {}

    def new_node(self):
        self.nodes_data.append('leaf')
        return len(self.nodes_data) - 1

    def get_children(self, node):
        if self.nodes_data[node] == 'leaf':
            self.nodes_data[node] = [self.new_node(), self.new_node()]
        return self.nodes_data[node]

    def impose_equality(self, node1, node2):
        merges_to_perform = {frozenset({node1, node2})}
        while merges_to_perform:
            a, b = merges_to_perform.pop()
            a = self.get_base_node(a)
            b = self.get_base_node(b)
            if a != b:
                # The "replace" call yields the children to add to the merge queue, if necessary
                merges_to_perform.update(map(frozenset, self._replace_node(a, b)))
            # Once the queue runs out, search for duplicate expressions from the bottom up
            if not merges_to_perform:
                for a, node_data in enumerate(self.nodes_data):
                    if isinstance(node_data, list):
                        for b in range(a):
                            if self.nodes_data[b] == node_data:
                                merges_to_perform.add(frozenset({a, b}))

    def get_base_node(self, node):
        seq = [node]
        while isinstance(self.nodes_data[node], int):
            node = self.nodes_data[node]
            seq.append(node)
        return node

    def _replace_node(self, node1, node2):
        # Remove node1 from the graph, replacing all references to it with node2 and add a forwarding pointer
        # Yields the overlapping children of node1 and node2
        for i, node_data in enumerate(self.nodes_data):
            if isinstance(node_data, list):
                for j, child in enumerate(node_data):
                    if child == node1:
                        node_data[j] = node2

        if self.nodes_data[node2] == 'leaf':
            self.nodes_data[node2] = self.nodes_data[node1]
        elif self.nodes_data[node1] != 'leaf':
            for i in range(2):
                child1 = self.nodes_data[node1][i]
                child2 = self.nodes_data[node2][i]
                if child1 != child2:
                    yield child1, child2

        self.nodes_data[node1] = node2
        for name in self.node_aliases:
            if self.node_aliases[name] == node1:
                self.node_aliases[name] = node2

    def has_cycle(self):
        visited = [False] * len(self.nodes_data)
        for root in range(len(self.nodes_data)):
            root = self.get_base_node(root)
            if visited[root]:
                continue
            stack = [root]
            while stack:
                node = stack.pop()
                visited[node] = True
                if self.nodes_data[node] == 'leaf':
                    continue
                assert isinstance(self.nodes_data[node], list)
                for child in self.nodes_data[node]:
                    if child is None:
                        continue
                    child = self.get_base_node(child)
                    if child in stack or child == node:
                        return True
                    if not visited[child]:
                        # Re-visit this node after finishing with the child
                        stack.append(node)
                        stack.append(child)
                        break
            return False

    def print(self):
        print(f'EGraph with {sum(not isinstance(node_data, int) for node_data in self.nodes_data)} nodes')
        for node, node_data in enumerate(self.nodes_data):
            if isinstance(node_data, list):
                left, right = node_data
                print(f'  {self._format_node(node)} -> {left}, {right}')
        print(f'  Leaves: {", ".join(self._format_node(node) for node, node_data in enumerate(self.nodes_data) if node_data == "leaf")}')

    def _format_node(self, node):
        names = [name for name, node_id in self.node_aliases.items() if node_id == node]
        if names:
            return f'{node} ({", ".join(names)})'
        else:
            return str(node)


def expr_to_tree(expr, egraph, side):
    var_to_node = {}
    def descend(e, node):
        if isinstance(e, int):
            if e in var_to_node:
                if node != var_to_node[e]:
                    egraph.impose_equality(node, var_to_node[e])
            else:
                var_to_node[e] = node
                egraph.node_aliases[f'{side}{e}'] = node
        else:
            children = egraph.get_children(node)
            descend(e[0], children[0])
            descend(e[1], children[1])
    root = egraph.new_node()
    descend(expr, root)
    return root


def subexprs(expr, proper=False):
    if not proper:
        yield expr
    if isinstance(expr, tuple):
        yield from subexprs(expr[0])
        yield from subexprs(expr[1])


def is_confluent(expr, show_egraphs=False):
    for subexpr in subexprs(expr, proper=True):
        if isinstance(subexpr, tuple):
            egraph = EGraph()
            root1 = expr_to_tree(expr, egraph, 'L')
            root2 = expr_to_tree(subexpr, egraph, 'R')
            egraph.impose_equality(root1, root2)
            if show_egraphs:
                print(f'Matching {format_expr(expr)} with {format_expr(subexpr)}:')
                egraph.print()
                print()
            if not egraph.has_cycle():
                # The e-graph being cyclic means that if we try to match the expression with the
                # sub-expression, there is no finite solution. (The infinite expression E = E ◇ E
                # is always a solution)
                return False
    # If the expression cannot be matched with any sub-expression, it means that the reduction
    # loci when applying the reduction law are far apart, so there is a unique simplified form.
    return True


# Example: equation 477
# print(is_confluent((0, (1, (2, (0, 1)))), show_egraphs=True))

for i, eq in enumerate(eqs):
    if isinstance(eq[0], int) and isinstance(eq[1], tuple):
        if is_confluent(eq[1]):
            print(format_expr(eq[0]), '=', format_expr(eq[1]), f'     ({i+1})')
