from __future__ import annotations
from datetime import datetime
from typing import List, Tuple, Set, FrozenSet, Dict, Optional, Any
from itertools import chain, combinations
from collections import defaultdict
import networkx as nx

space: frozenset = frozenset({'E', '0.2', '0.4', '0.5'})
# (A, B, C, D) represents A|B ? C|D, where ? is either > or >=
Comparison = Tuple[frozenset, frozenset, frozenset, frozenset]


# Convert frozensets to sets and emptysets to the emptyset symbol for readability
def prt(a: frozenset) -> str:
    if len(a) == 0:
        return 'Ø'
    return ','.join(set(a)) if len(a) == 1 else '{' + ','.join(set(a)) + '}'
    # replace previous line with following line to always print out set brackets
    # return '{' + ','.join(set(a)) + '}'


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


# Finds the all-pairs shortest paths using the distance function d(P) = minimum weight edge in P
# The distance of a node to itself is set to infinity
def floyd_warshall_modified_distance(G):
    # dictionary-of-dictionaries representation for dist
    # use some defaultdict magick here
    # for dist the default is the floating point inf value
    dist = defaultdict(lambda: defaultdict(lambda: float('inf')))
    for u in G:
        dist[u][u] = float('inf')  # distance to self is inf
    # set distance to neighbors
    for u, v, weight in G.edges.data('weight', default=1.0):
        if u != v:
            dist[u][v] = min(weight, dist[u][v])
    for k in G:
        for i in G:
            for j in G:
                if i != j:
                    if (dist[i][k] != float('inf') and dist[k][j] != float('inf')):  # Check the path exists
                        dist[i][j] = min(dist[i][j], min(dist[i][k], dist[k][j]))
    return dict(dist)


class Ordering:
    qualcomps: Set[QualComparison]

    def __init__(self, qualcomps: Optional[Set[QualComparison]] = None):
        self.qualcomps = set()
        self.ax5dict: Dict[(frozenset, frozenset), Dict[int, Set[QualComparison]]] \
            = defaultdict(lambda: defaultdict(lambda: set()))
        self.ax6set = set()
        if qualcomps:
            for qc in qualcomps:
                self.add_comparison(qc)

    def add_comparison(self, qc: QualComparison):
        if qc not in self:
            self.qualcomps.add(qc)
            a1, c1, a2, c2 = qc.comparison
            self.ax5dict[(c1, c2)][len(a1) + len(a2)].add(qc)
            if c1 >= a1 and c2 >= a2:
                self.ax6set.add(qc)

    def __contains__(self, item: QualComparison):
        return item in self.qualcomps

    def __str__(self):
        return self.qualcomps.__str__()

    def __len__(self):
        return len(self.qualcomps)

    def axiom_5_closure(self: Ordering):
        dict: Dict[(frozenset, frozenset), Dict[int, Set[QualComparison]]] = self.ax5dict
        for (c1, c2), buckets in dict.items():  # orderings of the form a1|c1 > a2|c2
            # The comparisons are in buckets based on the |a1| + |a2|
            n = 2 * len(space)  # maximum bucket size
            # iterate over all buckets. When i = j, this checks all pairs within a bucket, otherwise across buckets.
            for i in range(0, n + 1):
                for j in range(i, n + 1):
                    if i + j <= 2 * n:
                        self.ax_5_bucket_cross_pairs(buckets[i], buckets[j])

    def ax_5_bucket_cross_pairs(self: Ordering, bucket1: Set[QualComparison], bucket2: Set[QualComparison]):
        for qc1 in bucket1:
            for qc2 in bucket2:
                a1, c1, a2, c2 = qc1.comparison
                b1, _, b2, _ = qc2.comparison
                if a1.isdisjoint(b1) and a2.isdisjoint(b2):
                    self.add_comparison(QualComparison((a1 | b1, c1, a2 | b2, c2), qc1.strict or qc2.strict))
                    # if either premise is strict, the conclusion is strict
        # note that the new comparison will be added to bucket[i+j], so we won't modify either bucket we're iterating over

    def axiom_6_closure(self: Ordering):
        comps_added: bool = True
        while comps_added:
            init_len = len(self)
            self.ax_6_helper()
            if len(self) == init_len:
                comps_added = False

    def ax_6_helper(self: Ordering):
        ax6set = self.ax6set.copy()
        for qc1 in ax6set:
            p, q, r, s = qc1.comparison
            for qc2 in ax6set:
                if qc2.comparison[1] == p and qc2.comparison[2] == s:
                    b, a, c_, b_ = qc1.comparison
                    c, _, _, a_ = qc2.comparison
                    new_comp = QualComparison((c, a, c_, a_), qc1.strict or qc2.strict)
                    # if new_comp not in self:
                    #     print("Premises: " + str(qc1) + ", " + str(qc2))
                    #     print("Conclusion: " + str(new_comp))
                    #     print()
                    self.add_comparison(new_comp)
                elif qc2.comparison[0] == q and qc2.comparison[3] == r:
                    b, a, c_, b_ = qc2.comparison
                    c, _, _, a_ = qc1.comparison
                    new_comp = QualComparison((c, a, c_, a_), qc1.strict or qc2.strict)
                    # if new_comp not in self:
                    #     print("Premises: " + str(qc1) + ", " + str(qc2))
                    #     print("Conclusion: " + str(new_comp))
                    #     print()
                    self.add_comparison(new_comp)

    # Represents the ordering as a graph and computes the transitive closure of the ordering
    def transitive_closure(self: Ordering):
        G = nx.DiGraph()
        # Create an edge of the form (A|B, C|D) for comparison A|B > C|D
        # The weight is 0 if it's a strict comparison, and 1 otherwise
        qcs = self.qualcomps
        for qc in qcs:
            comp = qc.comparison
            G.add_edge(tuple(comp[0:2]), tuple(comp[2:4]), weight=int(not qc.strict))
        distances = floyd_warshall_modified_distance(G)
        for src in G:
            for dst in G:
                if src != dst:
                    if distances[src][dst] == 0:  # at least one strict comparison used
                        self.add_comparison(QualComparison((src[0], src[1], dst[0], dst[1]), True))
                    elif distances[src][dst] == 1:  # reachable, by only non-strict comparisons
                        self.add_comparison(QualComparison((src[0], src[1], dst[0], dst[1]), False))

    # The seed includes the reflexive condition and Axioms 3 and 4
    def seed(self: Ordering):
        for A in powerset(space):
            for B in powerset(space):
                fs = frozenset
                self.add_comparison(QualComparison((fs(A), fs(B), fs(A), fs(B)), False))  # Reflexivity
                self.add_comparison(QualComparison((fs(A), fs(A), fs(B), fs(B)), False))  # Axiom 3a
                self.add_comparison(QualComparison((space, space, fs(A), fs(B)), False))  # Axiom 3b
                # Axiom 4
                self.add_comparison(QualComparison((fs(A) & fs(B), fs(B), fs(A), fs(B)), False))
                self.add_comparison(QualComparison((fs(A), fs(B), fs(A) & fs(B), fs(B)), False))

    # Checks if each pair of comparisons are compatible.
    # Returns false if there is a comparison of the form A|B > A|B
    # Doesn't check if a partial ordering can be extended to a consistent full ordering.
    def check_pairwise_sat(self: Ordering) -> bool:
        qcs = self.qualcomps
        for qc1 in qcs:
            comp = qc1.comparison
            if comp[0] == comp[2] and comp[1] == comp[3] and qc1.strict:  # A|B > A|B
                return False
            for qc2 in qcs:
                if qc1.contradicts(qc2):
                    return False
        return True

    # Given (A, B, C, D), checks if A|B >= C|D or C|D >= A|B (and for strictness). Returns the full QualComp
    def check_comparison(self, comparison: Comparison) -> Optional[QualComparison]:
        qcs = {QualComparison(comparison, True), QualComparison(comparison, False),
               QualComparison(flip_helper(comparison), True), QualComparison(flip_helper(comparison), False)}
        for qc in qcs:
            if qc in self.qualcomps:
                return qc
        return None


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


# Returns P_theta(E), where E is assumed to be an iid sequence of coin flips, with H for heads and T for fails
def likelihood(E: str, theta: float) -> float:
    heads = E.count('H')
    tails = E.count('T')
    return theta ** heads * (1 - theta) ** tails


def likelihood_comps(E: str, Theta: Set[str]) -> Set[QualComparison]:
    comps: Set[QualComparison] = set()
    for theta1 in Theta:
        for theta2 in Theta:
            fs = frozenset
            p1 = likelihood(E, float(theta1))
            p2 = likelihood(E, float(theta2))
            if p1 > p2:
                comps.add(QualComparison((fs('E'), fs([theta1]), fs('E'), fs([theta2])), True))
            elif p2 > p1:
                comps.add(QualComparison((fs('E'), fs([theta2]), fs('E'), fs([theta1])), True))
            else:
                comps.add(QualComparison((fs('E'), fs([theta1]), fs('E'), fs([theta2])), False))
                comps.add(QualComparison((fs('E'), fs([theta2]), fs('E'), fs([theta1])), False))
    return comps


def Q(prior_prob: Dict[str, float], A: FrozenSet[str]) -> float:
    res = 0
    for theta in A:
        res += prior_prob[theta]
    return res


# Adds a probabilistic prior, adding all comparisons of the form A|Δ >= B|Δ, for A, B
def prob_prior_comps(prior_prob: Dict[str, float]) -> Set[QualComparison]:
    comps: Set[QualComparison] = set()
    for A in powerset(prior_prob.keys()):
        for B in powerset(prior_prob.keys()):
            fs = frozenset
            p1 = Q(prior_prob, A)
            p2 = Q(prior_prob, B)
            if p1 > p2:
                comps.add(QualComparison((fs(A), space, fs(B), space), True))
            elif p2 > p1:
                comps.add(QualComparison((fs(B), space, fs(A), space), True))
            else:
                comps.add(QualComparison((fs(A), space, fs(B), space), False))
                comps.add(QualComparison((fs(B), space, fs(A), space), False))
    return comps


# Adds the non probabilistic prior discussed in Krantz, where |Theta| = 5
def krantz_prior_comps() -> Set[QualComparison]:
    return


def print_stats(start_time, ordering, msg=None):
    if msg:
        print(msg)
    print(ordering)
    print("Time: " + str(datetime.now() - start_time))
    print("Number of comparisons: " + str(len(ordering)))
    print("Size of Ax6Set: " + str(len(ordering.ax6set)))
    print("***********")
    print()


def test_prob_prior():
    prior_probs: Dict[str, float] = {'0.2': 0.05, '0.4': 0.45, '0.5': 0.5}

    print(set(prior_probs.keys()))
    # Add comparisons from likelihoods and prior over hypotheses
    ordering = Ordering(likelihood_comps('TTTTH', set(prior_probs.keys())))
    print(ordering)
    qual_comps = prob_prior_comps(prior_probs)
    for qc in qual_comps:
        ordering.add_comparison(qc)
    print(ordering)

    # Add comparisons via the axioms
    ordering.seed()
    ordering.axiom_5_closure()
    ordering.axiom_6_closure()
    ordering.transitive_closure()
    # print("Consistent Ordering: ", ordering.check_pairwise_sat())
    print("Length: ",  len(ordering))

    # Check for all comparisons of the form H|E >= H'|E
    fs = frozenset
    for A in powerset(prior_probs.keys()):
        for B in powerset(prior_probs.keys()):
            comp: Comparison = (fs(A), fs('E'), fs(B), fs('E'))
            qc = ordering.check_comparison(comp)
            if qc is None:
                print("No comparison for: " + str([prt(a) for a in comp]))
            else:
                print(qc)


def test_orderings():
    start_time = datetime.now()
    c1 = [{'A', 'B'}, {'C'}, {'A'}, {'D'}]
    c2 = [{'A'}, {'C'}, {'B'}, {'D'}]
    c3 = [{'E'}, {'C'}, {'F'}, {'D'}]
    c4 = [{'E'}, {'F'}, {'E'}, {'F'}]

    qc1 = QualComparison(tuple(frozenset(s) for s in c1), True)
    qc2 = QualComparison(tuple(frozenset(s) for s in c2), False)
    qc3 = QualComparison(tuple(frozenset(s) for s in c3), False)
    qc4 = QualComparison(tuple(frozenset(s) for s in c4), True)

    # ordering = Ordering({qc1, qc2, qc3})
    # print(ordering)
    # axiom_5_closure(ordering)
    # print(ordering)

    ordering: Ordering = Ordering()
    ordering.seed()
    print_stats(start_time, ordering, "After seed")

    ordering.axiom_5_closure()
    print_stats(start_time, ordering, "After A6")

    ordering.axiom_6_closure()
    print_stats(start_time, ordering, "After A5")

    print(ordering.check_pairwise_sat())
    print_stats(start_time, ordering, "After sat check")

    ordering.transitive_closure()
    print_stats(start_time, ordering, "After TC")
    ordering.add_comparison(qc1)
    ordering.axiom_5_closure()
    print_stats(start_time, ordering, "After A5")

    ordering.axiom_6_closure()
    print_stats(start_time, ordering, "After A6")

    ordering.transitive_closure()
    print_stats(start_time, ordering, "After TC")


test_prob_prior()
