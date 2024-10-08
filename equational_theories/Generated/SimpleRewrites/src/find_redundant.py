#!/usr/bin/env python3

import sys
import re
import os
from collections import defaultdict, deque

def read_implications(f):
    implications = []
    nodes = set()
    if True:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if '_implies_' not in line:
                continue  # Skip invalid lines
            lhs, rhs = line.split('_implies_')
            implications.append((lhs, rhs))
            nodes.update([lhs, rhs])
        return implications, nodes

def build_graph(implications):
    graph = defaultdict(set)
    for src, dst in implications:
        graph[src].add(dst)
    return graph

def find_alternative_path(graph, src, dst, removed_edge):
    visited = set()
    queue = deque()
    queue.append((src, [src]))
    while queue:
        node, path = queue.popleft()
        if node == dst and len(path) > 1:
            return path
        for neighbor in graph[node]:
            if (node, neighbor) == removed_edge:
                continue
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append((neighbor, path + [neighbor]))
    return None

def find_unnecessary_implications(implications, graph):
    unnecessary = []
    for src, dst in implications:
        # Temporarily remove the edge src => dst
        graph[src].remove(dst)
        path = find_alternative_path(graph, src, dst, None)
        # Add the edge back
        graph[src].add(dst)
        if path:
            # Convert the path to a list of implications
            implication_path = []
            for i in range(len(path) - 1):
                implication_path.append(f"{path[i]}_implies_{path[i+1]}")
            unnecessary.append(((src, dst), implication_path))
    return unnecessary

def main():
    # hey, it works, ok?
    implies = os.popen('cat theorems/* | grep -o "Equation[0-9]*_implies_Equation[0-9]*"').readlines()
    implications, nodes = read_implications(implies)
    graph = build_graph(implications)
    unnecessary_implications = find_unnecessary_implications(implications, graph)

    rejects = set()
    for (src, dst), path in unnecessary_implications:
        rejects.add((src, dst))

    for f in os.listdir("theorems"):
        remaining_lines = []
        for line in open(os.path.join("theorems", f)).readlines():
            found = re.findall("(Equation[0-9]*)_implies_(Equation[0-9]*)", line)
            if len(found) != 0:
                (src, dst) = found[0]
                if (src,dst) in rejects:
                    continue
                else:
                    remaining_lines.append(line)
            else:
                remaining_lines.append(line)
        if 'theorem' in "".join(remaining_lines):
            open(os.path.join("theorems", f), "w").write("".join(remaining_lines))
        else:
            os.remove(os.path.join("theorems", f))
                
    
if __name__ == "__main__":
    main()

