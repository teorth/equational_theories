#!/usr/bin/env python3

import argparse
import json
import networkx as nx


class Weights:
    unconditional = 1
    implication = 10
    facts = 10
    dual = 1000
    conjecture = 1000000


def add_edge(G, src, dst, weight, **attrs):
    if not attrs["proven"]:
        weight *= Weights.conjecture
    if attrs["dual"]:
        weight *= Weights.dual
    if G.has_successor(src, dst):
        if weight > G[src][dst]["weight"]:
            return
    G.add_edge(src, dst, weight=weight, **attrs)


def neg(node):
    return node + "_neg"


def build_graph(entries, duals):
    G = nx.DiGraph()
    ctr = 0
    all_equations, unconditionals = set(), []
    for entry in entries:
        variant = entry["variant"]
        attrs = {
            "name": entry["name"],
            "filename": entry["filename"].split("equational_theories/")[-1],
            "proven": entry["proven"],
        }
        if eq := variant.get("unconditional"):
            G.add_node(eq)
            all_equations.add(eq)
            unconditionals.append((eq, attrs))
        if impl := variant.get("implication"):
            all_equations.add(impl["lhs"])
            all_equations.add(impl["rhs"])
            add_edge(G, impl["rhs"], impl["lhs"], Weights.implication, dual=False, **attrs)
            add_edge(G, neg(impl["rhs"]), neg(impl["lhs"]), Weights.implication, dual=False, **attrs)
            if impl["lhs"] in duals and impl["rhs"] in duals:
                add_edge(G, duals[impl["rhs"]], duals[impl["lhs"]], Weights.implication, dual=True, **attrs)
                add_edge(G, neg(duals[impl["rhs"]]), neg(duals[impl["lhs"]]), Weights.implication, dual=True, **attrs)
        if facts := variant.get("facts"):
            all_equations.update(facts["satisfied"])
            all_equations.update(facts["refuted"])
            node = f"Facts{ctr}"
            node_dual = f"Facts{ctr + 1}"
            ctr += 2
            for eq in facts["satisfied"]:
                add_edge(G, eq, node, Weights.facts, dual=False, **attrs)
                if eq in duals:
                    add_edge(G, duals[eq], node_dual, Weights.facts, dual=True, **attrs)
            for eq in facts["refuted"]:
                add_edge(G, node, neg(eq), Weights.facts, dual=False, **attrs)
                if eq in duals:
                    add_edge(G, node_dual, neg(duals[eq]), Weights.facts, dual=True, **attrs)
    for unconditional, attrs in unconditionals:
        for eq in all_equations:
            add_edge(G, unconditional, eq, Weights.unconditional, dual=False, **attrs)
            add_edge(G, neg(unconditional), neg(eq), Weights.unconditional, dual=False, **attrs)
            if unconditional in duals:
                add_edge(G, duals[unconditional], eq, Weights.unconditional, dual=True, **attrs)
                add_edge(G, neg(duals[unconditional]), neg(eq), Weights.unconditional, dual=True, **attrs)
    return G


def print_detailed_path(G, path, duals):
    if len(path) == 1:
        print(f"{path[0]} => {path[0]}  (tautology)")
    for i in range(len(path) - 1, 0, -1):
        if path[i - 1].startswith("Facts"):
            continue
        attrs = G[path[i - 1]][path[i]]
        if path[i].startswith("Facts"):
            lhs = path[i - 1].replace("_neg", "")
            rhs = path[i + 1].replace("_neg", "")
            print(lhs, " has a model that does not satisfy ", rhs, "" if attrs["proven"] else " (conjecture)")
            if attrs["dual"]:
                print(f"    proved for the dual: {duals[lhs]} =/=> {duals[rhs]}")
            print(f"    {attrs['name']}  in  {attrs['filename']}")
        else:
            rhs = path[i - 1].replace("_neg", "")
            lhs = path[i].replace("_neg", "")
            print(lhs, "=>", rhs, "" if attrs["proven"] else " (conjecture)")
            if attrs["dual"]:
                print(f"    proved for the dual: {duals[lhs]} => {duals[rhs]}")
            print(f"    {attrs['name']}  in  {attrs['filename']}")


def main():
    parser = argparse.ArgumentParser(description="List the inference steps showing that one "
                                                 "equation implies or does not imply another.")
    parser.add_argument("--entries-file", default="full_entries.json",
                        help="The output of extract_implications raw --full-entries")
    parser.add_argument("--duals-file", default="data/duals.json")
    parser.add_argument("lhs", help="Left-hand side equation")
    parser.add_argument("rhs", help="Right-hand side equation")

    args = parser.parse_args()
    entries = json.load(open(args.entries_file))
    duals = {f"Equation{i}": f"Equation{i}" for i in range(1, 4695)}
    for i, j in json.load(open(args.duals_file)):
        duals[f"Equation{i}"] = f"Equation{j}"
        duals[f"Equation{j}"] = f"Equation{i}"

    G = build_graph(entries, duals)

    path_yes, path_no = None, None
    try:
        path_yes = nx.shortest_path(G, args.rhs, args.lhs, weight="weight")
    except nx.NetworkXNoPath:
        pass

    try:
        path_no = nx.shortest_path(G, args.lhs, neg(args.rhs), weight="weight")
    except nx.NetworkXNoPath:
        pass

    if path_yes and path_no:
        print("Found contradiction!")
        print()
    if path_yes:
        print_detailed_path(G, path_yes, duals)
    if path_no:
        print_detailed_path(G, path_no, duals)
    if not path_yes and not path_no:
        print("Unknown")


if __name__ == "__main__":
    main()
