#!/usr/bin/env sage -python
"""Reproduce and exactly audit the small binary single-deletion LP claims.

Run with SageMath (the current checked environment is SageMath 10.9):

    sage -python VTlean/scripts/audit_deletion_lps.py

GLPK returns floating-point LP solutions.  This script reconstructs bounded-
denominator rationals and then checks every primal and dual inequality using
Python's exact ``Fraction`` arithmetic.  The solver output is therefore only
used to find candidate certificates; exact checks, not floating tolerances,
decide whether the claimed values are certified.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations

from sage.all import Graph
from sage.numerical.backends.glpk_backend import (
    glp_simplex_only,
    glp_simplex_or_intopt,
)
from sage.numerical.mip import MixedIntegerLinearProgram


RATIONAL_RECONSTRUCTION_DENOMINATOR = 100_000


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def all_words(n: int) -> list[str]:
    return [format(i, f"0{n}b") for i in range(2**n)]


def deletion_ball(word: str) -> frozenset[str]:
    return frozenset(word[:i] + word[i + 1 :] for i in range(len(word)))


def insertion_ball(word: str) -> frozenset[str]:
    return frozenset(
        word[:i] + bit + word[i:]
        for i in range(len(word) + 1)
        for bit in "01"
    )


def rationalize(value: float) -> Fraction:
    return Fraction(float(value)).limit_denominator(
        RATIONAL_RECONSTRUCTION_DENOMINATOR
    )


def set_simplex_only(lp: MixedIntegerLinearProgram) -> None:
    """Force GLPK's simplex algorithm so its row duals are available."""
    lp.get_backend().solver_parameter(glp_simplex_or_intopt, glp_simplex_only)


def vt_zero_code(n: int) -> list[str]:
    return [
        word
        for word in all_words(n)
        if sum((i + 1) * int(bit) for i, bit in enumerate(word)) % (n + 1) == 0
    ]


def audit_n6_fractional_clique_cover() -> None:
    """Check the manuscript's explicit weight-10 clique cover of {0,1}^6."""
    column_outputs = [
        "00000",
        "11111",
        "00001",
        "00011",
        "00111",
        "00110",
        "01100",
        "01111",
        "11110",
        "11100",
        "11000",
        "11001",
        "10011",
        "10000",
    ]
    non_helly = [
        ["001001", "010001", "010010", "010100", "010101", "011001", "101001"],
        ["001010", "010010", "100010", "100100", "100101", "100110", "101010"],
        ["010101", "011001", "011010", "011011", "011101", "101101", "110101"],
        ["010110", "100110", "101010", "101011", "101101", "101110", "110110"],
    ]

    cliques = [set(insertion_ball(y)) for y in column_outputs] + [
        set(clique) for clique in non_helly
    ]
    weights = [Fraction(1), Fraction(1)] + [Fraction(1, 2)] * 16
    require(len(cliques) == 18, "the listed cover should contain 18 cliques")

    words = all_words(6)
    balls = {word: deletion_ball(word) for word in words}
    for i, clique in enumerate(cliques):
        require(len(clique) == 7, f"listed clique {i} does not have size 7")
        for a, b in combinations(clique, 2):
            require(
                balls[a] & balls[b],
                f"listed set {i} is not a deletion-conflict clique: {a}, {b}",
            )

    # The four displayed exceptional cliques really are non-Helly: there is no
    # single length-5 output common to all seven words.
    for i, clique in enumerate(non_helly):
        common_outputs = set.intersection(*(set(balls[word]) for word in clique))
        require(not common_outputs, f"exceptional clique {i} is Helly")

    coverage = {word: Fraction(0) for word in words}
    for clique, weight in zip(cliques, weights):
        for word in clique:
            coverage[word] += weight

    total_weight = sum(weights, Fraction(0))
    min_coverage = min(coverage.values())
    code = vt_zero_code(6)
    require(len(code) == 10, "VT_0(6) should contain 10 words")
    require(
        all(not (balls[a] & balls[b]) for a, b in combinations(code, 2)),
        "VT_0(6) failed the direct deletion-collision check",
    )
    require(total_weight == 10, f"cover has unexpected weight {total_weight}")
    require(min_coverage >= 1, f"cover leaves a word undercovered: {min_coverage}")

    print(
        "n=6 full clique cover: 18 size-7 cliques; "
        f"weight={total_weight}; minimum coverage={min_coverage}; "
        f"|VT_0(6)|={len(code)}.  Hence alpha*=M(6)=10."
    )


def solve_column_packing_lp(n: int, show_certificates: bool) -> Fraction:
    """Solve nu*(A_n), then certify the optimum by exact rational checks."""
    words = all_words(n)
    outputs = all_words(n - 1)
    balls = {word: deletion_ball(word) for word in words}

    lp = MixedIntegerLinearProgram(solver="GLPK", maximization=True)
    x = lp.new_variable(real=True, nonnegative=True)
    lp.set_objective(sum(x[word] for word in words))
    for output in outputs:
        lp.add_constraint(
            sum(x[word] for word in words if output in balls[word]), max=1
        )
    set_simplex_only(lp)
    floating_optimum = lp.solve()

    primal_raw = lp.get_values(x)
    primal = {word: rationalize(primal_raw.get(word, 0)) for word in words}
    backend = lp.get_backend()
    dual = [rationalize(backend.get_row_dual(i)) for i in range(len(outputs))]

    # Exact primal feasibility for the row packing constraints.
    for word, value in primal.items():
        require(value >= 0, f"negative primal weight at {word}: {value}")
    for output in outputs:
        load = sum(
            (primal[word] for word in words if output in balls[word]), Fraction(0)
        )
        require(load <= 1, f"primal packing violates output {output}: {load}")

    # Exact dual feasibility: every length-n word sees total output weight >= 1.
    output_index = {word: i for i, word in enumerate(outputs)}
    for word in words:
        load = sum((dual[output_index[y]] for y in balls[word]), Fraction(0))
        require(load >= 1, f"dual cover misses word {word}: weight {load}")
    require(all(value >= 0 for value in dual), "negative dual output weight")

    primal_value = sum(primal.values(), Fraction(0))
    dual_value = sum(dual, Fraction(0))
    require(
        primal_value == dual_value,
        f"exact primal/dual objectives differ: {primal_value} vs {dual_value}",
    )
    require(
        abs(float(primal_value) - floating_optimum) < 1e-7,
        "rational certificate does not match GLPK's reported objective",
    )

    expected = {6: Fraction(41, 4), 7: Fraction(343, 20)}.get(n)
    if expected is not None:
        require(primal_value == expected, f"n={n}: expected {expected}, got {primal_value}")

    print(
        f"n={n} column packing: exact optimum={primal_value}; "
        f"GLPK={floating_optimum:.12g}; exact primal and dual checked."
    )
    if show_certificates:
        print(f"n={n} column-packing primal (word, weight):")
        print([(word, value) for word, value in primal.items() if value])
        print(f"n={n} column-packing dual (output, weight):")
        print([(output, value) for output, value in zip(outputs, dual) if value])
    return primal_value


def conflict_graph_and_maximal_cliques(n: int) -> tuple[list[str], list[frozenset[str]]]:
    words = all_words(n)
    outputs = all_words(n - 1)
    graph = Graph()
    graph.add_vertices(words)
    insertion_cliques = [insertion_ball(y) for y in outputs]
    for clique in insertion_cliques:
        graph.add_edges(combinations(sorted(clique), 2))

    maximal_cliques = [frozenset(clique) for clique in graph.cliques_maximal()]
    # Check that the graph generated from insertion balls is exactly the
    # pairwise deletion-conflict graph, not a strict subgraph.
    balls = {word: deletion_ball(word) for word in words}
    for a, b in combinations(words, 2):
        require(
            graph.has_edge(a, b) == bool(balls[a] & balls[b]),
            f"conflict graph mismatch at {a}, {b}",
        )
    return words, maximal_cliques


def v4_word_orbits(words: list[str]) -> tuple[list[list[str]], dict[str, int]]:
    def complement(word: str) -> str:
        return "".join("1" if bit == "0" else "0" for bit in word)

    def orbit(word: str) -> set[str]:
        reverse = word[::-1]
        return {word, reverse, complement(word), complement(reverse)}

    remaining = set(words)
    orbits: list[list[str]] = []
    while remaining:
        members = sorted(orbit(min(remaining)))
        require(set(members) <= remaining, "V4 orbits did not partition the words")
        orbits.append(members)
        remaining.difference_update(members)
    orbit_of = {
        word: i for i, members in enumerate(orbits) for word in members
    }
    require(set(orbit_of) == set(words), "incomplete V4 orbit partition")
    return orbits, orbit_of


def solve_fractional_clique_cover_n7(show_certificates: bool) -> Fraction:
    """Audit alpha*(G_del) at n=7 by exact primal/dual certificates."""
    n = 7
    words, maximal_cliques = conflict_graph_and_maximal_cliques(n)
    clique_count = len(maximal_cliques)
    require(clique_count == 992, f"expected 992 maximal cliques, found {clique_count}")

    outputs = all_words(n - 1)
    helly_cliques = {insertion_ball(output) for output in outputs}
    maximal_set = set(maximal_cliques)
    helly_maximal_count = len(helly_cliques & maximal_set)
    require(
        helly_maximal_count == 64,
        f"expected 64 maximal Helly cliques, found {helly_maximal_count}",
    )

    # Primal: a fractional cover by all maximal cliques.
    clique_indices_by_word = {
        word: [i for i, clique in enumerate(maximal_cliques) if word in clique]
        for word in words
    }
    cover_lp = MixedIntegerLinearProgram(solver="GLPK", maximization=False)
    z = cover_lp.new_variable(real=True, nonnegative=True)
    cover_lp.set_objective(sum(z[i] for i in range(clique_count)))
    for word in words:
        cover_lp.add_constraint(
            sum(z[i] for i in clique_indices_by_word[word]), min=1
        )
    set_simplex_only(cover_lp)
    floating_cover_optimum = cover_lp.solve()
    z_raw = cover_lp.get_values(z)
    cover_weights = [rationalize(z_raw.get(i, 0)) for i in range(clique_count)]
    require(all(weight >= 0 for weight in cover_weights), "negative clique-cover weight")
    for word in words:
        amount = sum(
            (cover_weights[i] for i in clique_indices_by_word[word]), Fraction(0)
        )
        require(amount >= 1, f"fractional clique cover misses {word}: {amount}")
    cover_value = sum(cover_weights, Fraction(0))

    # Dual: use V4-orbit-constant word weights.  These are expanded back to
    # all 128 words and checked against every maximal clique, so the resulting
    # vector itself is a full-graph dual certificate.
    orbits, orbit_of = v4_word_orbits(words)
    dual_lp = MixedIntegerLinearProgram(solver="GLPK", maximization=True)
    u = dual_lp.new_variable(real=True, nonnegative=True)
    dual_lp.set_objective(sum(len(members) * u[i] for i, members in enumerate(orbits)))
    for clique in maximal_cliques:
        dual_lp.add_constraint(sum(u[orbit_of[word]] for word in clique), max=1)
    set_simplex_only(dual_lp)
    floating_dual_optimum = dual_lp.solve()
    u_raw = dual_lp.get_values(u)
    orbit_weights = [rationalize(u_raw.get(i, 0)) for i in range(len(orbits))]
    word_weights = {
        word: orbit_weights[orbit_of[word]] for word in words
    }
    require(all(weight >= 0 for weight in word_weights.values()), "negative vertex dual weight")
    for clique in maximal_cliques:
        load = sum((word_weights[word] for word in clique), Fraction(0))
        require(load <= 1, f"dual clique constraint violated: load {load}")
    dual_value = sum(word_weights.values(), Fraction(0))

    require(
        cover_value == dual_value,
        f"exact clique-cover primal/dual differ: {cover_value} vs {dual_value}",
    )
    require(
        abs(float(cover_value) - floating_cover_optimum) < 1e-7,
        "exact cover certificate differs from GLPK objective",
    )
    require(
        abs(float(dual_value) - floating_dual_optimum) < 1e-7,
        "exact dual certificate differs from GLPK objective",
    )
    require(dual_value == Fraction(662, 39), f"expected 662/39, got {dual_value}")

    print(
        "n=7 full fractional clique cover: "
        f"{clique_count} maximal cliques ({helly_maximal_count} Helly, "
        f"{clique_count - helly_maximal_count} non-Helly); "
        f"exact primal=dual={dual_value}; certificates checked."
    )

    if show_certificates:
        print("n=7 full-cover primal certificate (clique words, weight):")
        print(
            [
                (sorted(maximal_cliques[i]), weight)
                for i, weight in enumerate(cover_weights)
                if weight
            ]
        )
        print("n=7 full-cover dual certificate (V4 orbit representative, weight):")
        print(
            [
                (members[0], orbit_weights[i], len(members))
                for i, members in enumerate(orbits)
                if orbit_weights[i]
            ]
        )
    return dual_value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--show-certificates",
        action="store_true",
        help="print sparse rational witnesses from the length-7 LPs",
    )
    args = parser.parse_args()

    audit_n6_fractional_clique_cover()
    solve_column_packing_lp(6, args.show_certificates)
    solve_column_packing_lp(7, args.show_certificates)
    solve_fractional_clique_cover_n7(args.show_certificates)
    print("All listed LP values and finite certificates passed exact checks.")


if __name__ == "__main__":
    main()
