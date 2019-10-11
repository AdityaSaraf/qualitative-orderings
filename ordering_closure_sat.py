from __future__ import annotations
from typing import List, Tuple, Set, FrozenSet, Dict, Optional
from itertools import chain, combinations
import networkx as nx

space: frozenset = frozenset({'A', 'B', 'C', 'D'})
# (A, B, C, D) represents A|B ? C|D, where ? is either > or >=
Comparison = Tuple[frozenset, frozenset, frozenset, frozenset]


# Convert frozensets to sets and emptysets to the emptyset symbol for readability
def prt(a: frozenset) -> str:
    if len(a) == 0:
        return 'Ø'
    # return ','.join(set(a))
    # replace previous line with following line to print out set brackets
    return '{' + ','.join(set(a)) + '}'


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


class Ordering:

    def __init__(self, qualcomps: Optional[Set[QualComparison]] = None,
                 ax5dict: Optional[Dict[(frozenset, frozenset), Set[QualComparison]]] = None):
        self.ax5dict = ax5dict if ax5dict else {}
        self.qualcomps = qualcomps if qualcomps else set()

    def add_comparison(self, qc: QualComparison):
        self.qualcomps.add(qc)
        key = (qc.comparison[1], qc.comparison[3])
        self.ax5dict[key].add(qc)


class QualComparison:

    def __init__(self, comparison: Comparison, strict: bool):
        self.strict = strict
        self.comparison: Comparison = comparison

    def flip_self(self):
        self.comparison = flip_helper(self.comparison)
        self.strict = not self.strict

    # Currently just checks if the two comparisons are directly opposed.
    # Can add more complicated contradiction functionality.
    def contradicts(self, other: QualComparison) -> bool:
        if self.strict or other.strict:
            if flip_helper(self.comparison) == other.comparison:
                return True
        return False

    def __str__(self):
        relation = '>' if self.strict else '≥'
        comp = self.comparison
        return f'{prt(comp[0])}|{prt(comp[1])}' + relation + f'{prt(comp[2])}|{prt(comp[3])}'

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, QualComparison):
            return (self.comparison, self.strict) == (other.comparison, other.strict)
        return False

    def __hash__(self):
        return hash((self.comparison, self.strict))


def flip_helper(comp: Comparison) -> Comparison:
    return (comp[2], comp[3], comp[0], comp[1])


def flip(qc: QualComparison) -> QualComparison:
    return QualComparison(flip_helper(qc.comparison), not qc.strict)


# Represents the ordering as a graph and computes the transitive, reflexive closure of the ordering
def transitive_reflexive_closure(ordering: Set[QualComparison]) -> Set[QualComparison]:
    G = nx.DiGraph()
    # Create an edge of the form (A|B, C|D) for comparison A|B > C|D
    # The weight is 1 if it's a strict comparison, and 0 otherwise
    for qc in ordering:
        comp = qc.comparison
        G.add_edge(tuple(comp[0:2]), tuple(comp[2:4]), weight=int(qc.strict))
    distances = nx.floyd_warshall(G)
    for src in distances.keys():
        for dst in distances[src]:
            if distances[src][dst] == 0:  # only non-strict relations used
                ordering.add(QualComparison((src[0], src[1], dst[0], dst[1]), False))
            elif distances[src][dst] != float('inf'):  # reachable, by strict relation
                ordering.add(QualComparison((src[0], src[1], dst[0], dst[1]), True))


# The seed includes the reflexive condition and Axioms 3 and 4
def seed() -> Ordering:
    ordering = Ordering()
    for A in powerset(space):
        for B in powerset(space):
            fs = frozenset
            ordering.add_comparison(QualComparison((fs(A), fs(B), fs(A), fs(B)), False))  # Reflexivity
            ordering.add_comparison(QualComparison((fs(A), fs(A), fs(B), fs(B)), False))  # Axiom 3a
            ordering.add_comparison(QualComparison((space, space, fs(A), fs(B)), False))  # Axiom 3b
            # Axiom 4
            ordering.add_comparison(QualComparison((fs(A) & fs(B), fs(B), fs(A), fs(B)), False))
            ordering.add_comparison(QualComparison((fs(A), fs(B), fs(A) & fs(B), fs(B)), False))
    return ordering


# Don't need to worry about applying Ax 4 to new clauses because of the idempotency of intersection
def axiom_4(ordering: Set[QualComparison]) -> Set[QualComparison]:
    for qc in ordering:
        x, y, w, z = qc.comparison
        ordering.add(QualComparison((x & y, y, w, z), qc.strict))
        ordering.add(QualComparison((x, y, w & z, z), qc.strict))
        ordering.add(QualComparison((x & y, y, w & z, z), qc.strict))


# Checks if each pair of comparisons are compatible.
# Returns false if there is a comparison of the form A|B > A|B
# Doesn't check if a partial ordering can be extended to a consistent full ordering.
def check_pairwise_sat(ordering: Set[QualComparison]) -> bool:
    for qc1 in ordering:
        comp = qc1.comparison
        if comp[0] == comp[2] and comp[1] == comp[3] and qc1.strict:  # A|B > A|B
            return False
        for qc2 in ordering:
            if qc1.contradicts(qc2):
                return False
    return True


def main():
    c1 = [{'A'}, {'B'}, {'C', 'D'}, {'D'}]
    c2 = [{'C'}, {'D'}, {'E'}, {'F'}]
    c3 = [{'X'}, {'Y'}, {'C'}, {'D'}]
    c4 = [{'E'}, {'F'}, {'A'}, {'B'}]
    qc1 = QualComparison(tuple(frozenset(s) for s in c1), True)
    qc2 = QualComparison(tuple(frozenset(s) for s in c2), False)
    qc3 = QualComparison(tuple(frozenset(s) for s in c3), False)
    qc4 = QualComparison(tuple(frozenset(s) for s in c4), False)
    ordering = seed()
    print(ordering)
    print(check_pairwise_sat(ordering))
    transitive_reflexive_closure(ordering)
    print(ordering)
    print(check_pairwise_sat(ordering))


main()
