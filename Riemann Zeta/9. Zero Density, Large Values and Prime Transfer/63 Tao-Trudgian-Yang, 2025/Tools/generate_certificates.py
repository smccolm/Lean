#!/usr/bin/env python3
"""Deterministically extract frozen rational data into a Lean module."""

from __future__ import annotations

import argparse
import ast
from fractions import Fraction
import hashlib
from math import gcd, lcm
import re
import zipfile
from pathlib import Path


ARCHIVE_SHA256 = "6ab14c1fbafe048abb61e497322cd7bb67868b2d8816fad0ec20183d937bb2f3"
DERIVED_PATH = "expdb-9953003/blueprint/src/python/derived.py"
ZERO_DENSITY_PATH = "expdb-9953003/blueprint/src/python/zero_density_estimate.py"
ZERO_DENSITY_ENERGY_PATH = (
    "expdb-9953003/blueprint/src/chapter/zero_density_energy.tex"
)
EXPECTED = [
    (89, 1282, 997, 1282),
    (652397, 9713986, 7599781, 9713986),
    (10769, 351096, 609317, 702192),
    (89, 3478, 15327, 17390),
]
EXPECTED_BOURGAIN_CANDIDATES = [
    (11, 85, 59, 85),
    (391, 4595, 3461, 4595),
    (2779, 38033, 58699, 76066),
    (89, 1282, 997, 1282),
    (652397, 9713986, 7599781, 9713986),
    (2371, 43205, 280013, 345640),
    (9, 217, 1461, 1736),
    (10769, 351096, 609317, 702192),
    (89, 3478, 15327, 17390),
    (1, 100, 14, 15),
]
PAPER_BOURGAIN_CANDIDATE_COUNT = 8
ENERGY_SPECS = [
    ("imp-hb-energy-bound", Fraction(3, 4), Fraction(5, 6), 2),
    ("imp-energy-bound2", Fraction(7, 10), Fraction(3, 4), 2),
    ("imp-energy-bound9", Fraction(173, 229), Fraction(443, 586), 3),
    ("imp-energy-bound10", Fraction(443, 586), Fraction(373, 493), 2),
    ("imp-energy-bound11", Fraction(373, 493), Fraction(103, 136), 3),
    ("imp-energy-bound4", Fraction(103, 136), Fraction(42, 55), 2),
    ("imp-energy-bound6", Fraction(42, 55), Fraction(79, 103), 2),
    ("imp-energy-bound7", Fraction(79, 103), Fraction(84, 109), 2),
    ("imp-energy-bound8", Fraction(84, 109), Fraction(5, 6), 2),
]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_frozen_source(archive: Path, member: str) -> str:
    if sha256(archive) != ARCHIVE_SHA256:
        raise SystemExit("paper-time ANTEDB archive SHA-256 mismatch")
    with zipfile.ZipFile(archive) as source:
        return source.read(member).decode("utf-8")


def extract_pairs(archive: Path) -> list[tuple[int, int, int, int]]:
    text = read_frozen_source(archive, DERIVED_PATH)
    pattern = re.compile(
        r"^\s*prove_exponent_pair\(frac\((\d+),(\d+)\),\s*"
        r"frac\((\d+),(\d+)\),\s*simplify_deps=False,\s*verbose=True\)",
        re.MULTILINE,
    )
    pairs = [tuple(map(int, match.groups())) for match in pattern.finditer(text)]
    if pairs != EXPECTED:
        raise SystemExit(f"unexpected frozen exponent-pair data: {pairs!r}")
    return pairs


def extract_bourgain_candidates(archive: Path) -> list[tuple[int, int, int, int]]:
    text = read_frozen_source(archive, ZERO_DENSITY_PATH)
    function = text[text.index("def bourgain_ep_to_zd():"):]
    block = function[function.index("    eps = ["):function.index("    bounds = []")]
    pattern = re.compile(
        r"\(frac\((\d+),\s*(\d+)\),\s*frac\((\d+),\s*(\d+)\)\)"
    )
    candidates = [tuple(map(int, match.groups())) for match in pattern.finditer(block)]
    if candidates != EXPECTED_BOURGAIN_CANDIDATES:
        raise SystemExit(f"unexpected frozen Bourgain candidate data: {candidates!r}")
    return candidates


def normalized_bound(k: Fraction, ell: Fraction) -> tuple[int, int, int]:
    values = [4 * k, 2 * (1 + k), -1 - ell]
    common_denominator = lcm(*(value.denominator for value in values))
    integers = [value.numerator * (common_denominator // value.denominator)
                for value in values]
    common_factor = gcd(gcd(abs(integers[0]), abs(integers[1])), abs(integers[2]))
    return tuple(value // common_factor for value in integers)


def crossover(left: tuple[int, int, int], right: tuple[int, int, int]) -> Fraction:
    left_num, left_slope, left_constant = left
    right_num, right_slope, right_constant = right
    denominator = left_num * right_slope - right_num * left_slope
    numerator = right_num * left_constant - left_num * right_constant
    if denominator == 0:
        raise SystemExit("parallel Bourgain candidate bounds")
    return Fraction(numerator, denominator)


def value_at(bound: tuple[int, int, int], sigma: Fraction) -> Fraction:
    numerator, slope, constant = bound
    denominator = slope * sigma + constant
    if denominator <= 0:
        raise SystemExit("nonpositive Bourgain denominator on an active interval")
    return Fraction(numerator, denominator)


def bourgain_threshold(k: Fraction, ell: Fraction) -> Fraction:
    threshold = max(Fraction(1, 2), (ell + 1) / (2 * (k + 1)))
    if k > Fraction(11, 85):
        threshold = max(
            threshold,
            (144 * k - 11 * ell - 11) / (170 * k - 22),
        )
    return threshold


def bourgain_pieces(
    candidates: list[tuple[int, int, int, int]],
) -> list[tuple[int, Fraction, Fraction, Fraction, Fraction, tuple[int, int, int]]]:
    selected = candidates[:PAPER_BOURGAIN_CANDIDATE_COUNT]
    rational_candidates = [
        (Fraction(k_num, k_den), Fraction(l_num, l_den))
        for k_num, k_den, l_num, l_den in selected
    ]
    bounds = [normalized_bound(k, ell) for k, ell in rational_candidates]
    endpoints = [Fraction(3, 4)]
    endpoints.extend(crossover(bounds[index], bounds[index + 1])
                     for index in range(len(bounds) - 1))
    endpoints.append(Fraction(1))

    pieces = []
    for index, ((k, ell), bound, lower, upper) in enumerate(
        zip(rational_candidates, bounds, endpoints, endpoints[1:])
    ):
        if not lower < upper:
            raise SystemExit("Bourgain envelope endpoints are not strictly increasing")
        midpoint = (lower + upper) / 2
        if midpoint <= bourgain_threshold(k, ell):
            raise SystemExit(f"candidate {index} is not admissible on its active interval")
        active_value = value_at(bound, midpoint)
        for (other_k, other_ell), other in zip(rational_candidates, bounds):
            if (midpoint > bourgain_threshold(other_k, other_ell)
                    and active_value > value_at(other, midpoint)):
                raise SystemExit(f"candidate {index} is not minimal on its active interval")
        pieces.append((index, k, ell, lower, upper, bound))
    return pieces


def rational(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def braced_group(text: str, start: int) -> tuple[str, int]:
    if start >= len(text) or text[start] != "{":
        raise SystemExit("expected a braced TeX group")
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1:index], index + 1
    raise SystemExit("unterminated braced TeX group")


def latex_fractions(text: str) -> list[tuple[str, str]]:
    fractions = []
    cursor = 0
    while True:
        marker = text.find(r"\frac", cursor)
        if marker < 0:
            return fractions
        numerator, after_numerator = braced_group(text, marker + len(r"\frac"))
        denominator, cursor = braced_group(text, after_numerator)
        fractions.append((numerator, denominator))


def linear_expression(expression: str) -> tuple[int, int]:
    source = re.sub(r"\s+", "", expression)
    source = source.replace(r"\left", "").replace(r"\right", "")
    source = source.replace(r"\sigma", "x")
    source = source.replace("{", "(").replace("}", ")")
    source = re.sub(r"(?<=\d)(?=[x(])", "*", source)
    source = re.sub(r"(?<=x)(?=\()", "*", source)
    source = re.sub(r"\)(?=\()", ")*(", source)

    def visit(node: ast.AST) -> tuple[int, int]:
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return 0, node.value
        if isinstance(node, ast.Name) and node.id == "x":
            return 1, 0
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            slope, constant = visit(node.operand)
            return -slope, -constant
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
            left_slope, left_constant = visit(node.left)
            right_slope, right_constant = visit(node.right)
            sign = 1 if isinstance(node.op, ast.Add) else -1
            return (left_slope + sign * right_slope,
                    left_constant + sign * right_constant)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
            left_slope, left_constant = visit(node.left)
            right_slope, right_constant = visit(node.right)
            if left_slope != 0 and right_slope != 0:
                raise SystemExit(f"nonlinear TeX expression: {expression!r}")
            return (left_slope * right_constant + right_slope * left_constant,
                    left_constant * right_constant)
        raise SystemExit(f"unsupported TeX expression: {expression!r}")

    return visit(ast.parse(source, mode="eval"))


def extract_energy_clauses(
    archive: Path,
) -> list[tuple[str, Fraction, Fraction, list[tuple[int, int, int, int]]]]:
    text = read_frozen_source(archive, ZERO_DENSITY_ENERGY_PATH)
    clauses = []
    for label, target_lower, target_upper, expected_count in ENERGY_SPECS:
        label_marker = rf"\label{{{label}}}"
        label_position = text.index(label_marker)
        theorem_start = text.rfind(r"\begin{theorem}", 0, label_position)
        theorem_end = text.index(r"\end{theorem}", label_position)
        theorem = text[theorem_start:theorem_end]
        range_match = re.search(
            r"For\s*\$(\d+)/(\d+)\s*\\le\s*\\sigma\s*\\le\s*"
            r"(\d+)/(\d+)\$",
            theorem,
        )
        if range_match is None:
            raise SystemExit(f"could not extract source range for {label}")
        range_values = tuple(map(int, range_match.groups()))
        source_lower = Fraction(range_values[0], range_values[1])
        source_upper = Fraction(range_values[2], range_values[3])
        if not (source_lower <= target_lower <= target_upper <= source_upper):
            raise SystemExit(f"target range is not covered by source theorem {label}")
        maximum = theorem[theorem.index(r"\max"):]
        fractions = latex_fractions(maximum)
        if len(fractions) != expected_count:
            raise SystemExit(
                f"expected {expected_count} energy bounds in {label}, got {fractions!r}"
            )
        bounds = []
        midpoint = (target_lower + target_upper) / 2
        for numerator_text, denominator_text in fractions:
            compact_denominator = re.sub(r"\s+", "", denominator_text)
            compact_denominator = compact_denominator.replace(r"\sigma", "x")
            if not compact_denominator.endswith("(1-x)"):
                raise SystemExit(f"missing (1-sigma) factor in {label}")
            compact_denominator = compact_denominator[:-len("(1-x)")]
            numerator_slope, numerator_constant = linear_expression(numerator_text)
            denominator_slope, denominator_constant = linear_expression(
                compact_denominator
            )
            if denominator_slope * midpoint + denominator_constant < 0:
                numerator_slope = -numerator_slope
                numerator_constant = -numerator_constant
                denominator_slope = -denominator_slope
                denominator_constant = -denominator_constant
            if denominator_slope * midpoint + denominator_constant <= 0:
                raise SystemExit(f"nonpositive normalized denominator in {label}")
            bounds.append((numerator_slope, numerator_constant,
                           denominator_slope, denominator_constant))
        clauses.append((label, target_lower, target_upper, bounds))
    return clauses


def render(
    pairs: list[tuple[int, int, int, int]],
    pieces: list[tuple[int, Fraction, Fraction, Fraction, Fraction,
                       tuple[int, int, int]]],
    energy_clauses: list[
        tuple[str, Fraction, Fraction, list[tuple[int, int, int, int]]]
    ],
) -> str:
    entries = "\n".join(
        f"  ({k_num} / {k_den}, {l_num} / {l_den})" +
        ("," if index + 1 < len(pairs) else "")
        for index, (k_num, k_den, l_num, l_den) in enumerate(pairs)
    )
    piece_definitions = []
    piece_names = []
    for ordinal, (candidate_index, k, ell, lower, upper, bound) in enumerate(pieces, 1):
        numerator, denominator_slope, denominator_constant = bound
        name = f"generatedBourgainPiece{ordinal}"
        piece_names.append(f"  {name}" + ("," if ordinal < len(pieces) else ""))
        piece_definitions.append(f"""/-- Exact lower-envelope piece {ordinal}, derived from frozen candidate {candidate_index}. -/
def {name} : GeneratedBourgainDensityPiece where
  candidateIndex := {candidate_index}
  k := {rational(k)}
  ell := {rational(ell)}
  lower := {rational(lower)}
  upper := {rational(upper)}
  bound :=
    {{ numeratorSlope := 0, numeratorConstant := {numerator},
      denominatorSlope := {denominator_slope},
      denominatorConstant := {denominator_constant} }}
""")
    energy_definitions = []
    energy_names = []
    for ordinal, (label, lower, upper, bounds) in enumerate(energy_clauses, 1):
        name = f"generatedEnergyClause{ordinal}"
        energy_names.append(f"  {name}" + ("," if ordinal < len(energy_clauses) else ""))
        rendered_bounds = "\n".join(
            "    { numeratorSlope := " + str(numerator_slope) +
            ", numeratorConstant := " + str(numerator_constant) +
            ", denominatorSlope := " + str(denominator_slope) +
            ", denominatorConstant := " + str(denominator_constant) + " }" +
            ("," if index + 1 < len(bounds) else "")
            for index, (numerator_slope, numerator_constant,
                        denominator_slope, denominator_constant) in enumerate(bounds)
        )
        energy_definitions.append(f"""/-- Exact clause {ordinal} data extracted from `{label}` in the frozen blueprint. -/
def {name} : GeneratedEnergyClause where
  sourceLabel := "{label}"
  lower := {rational(lower)}
  upper := {rational(upper)}
  bounds := [
{rendered_bounds}
  ]
""")
    return f"""-- This file is generated by Tools/generate_certificates.py.
-- Source: ANTEDB commit 9953003a48f46fe8075ccf9534321f98f656032e.
-- Do not edit by hand.

import TaoTrudgianYang2025.ExponentPair
import TaoTrudgianYang2025.RationalCertificates

namespace TaoTrudgianYang2025

/-- The four output points extracted from the frozen paper-time driver. -/
def generatedExponentPairCoordinates : List (ℚ × ℚ) := [
{entries}
]

theorem generatedExponentPairCoordinates_count :
    generatedExponentPairCoordinates.length = 4 := by
  rfl

/-- One exact rational piece of the paper's eight-piece Bourgain envelope. -/
structure GeneratedBourgainDensityPiece where
  candidateIndex : Nat
  k : ℚ
  ell : ℚ
  lower : ℚ
  upper : ℚ
  bound : RationalAffineFraction

{"".join(piece_definitions)}
/-- The eight source-theorem pieces reconstructed by exact rational arithmetic
from the first eight candidates in the frozen optimization driver. -/
def generatedBourgainDensityPieces : List GeneratedBourgainDensityPiece := [
{chr(10).join(piece_names)}
]

theorem generatedBourgainDensityPieces_count :
    generatedBourgainDensityPieces.length = 8 := by
  rfl

/-- One source clause for `A*(sigma) * (1-sigma)`, represented as the maximum
of exact rational affine fractions on a closed rational interval. -/
structure GeneratedEnergyClause where
  sourceLabel : String
  lower : ℚ
  upper : ℚ
  bounds : List RationalAffineFraction

{"".join(energy_definitions)}
/-- All nine additive-energy clauses extracted from the frozen ANTEDB
blueprint, restricted to the exact intervals in the paper's public theorem. -/
def generatedEnergyClauses : List GeneratedEnergyClause := [
{chr(10).join(energy_names)}
]

theorem generatedEnergyClauses_count :
    generatedEnergyClauses.length = 9 := by
  rfl

end TaoTrudgianYang2025
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    content = render(
        extract_pairs(args.archive),
        bourgain_pieces(extract_bourgain_candidates(args.archive)),
        extract_energy_clauses(args.archive),
    )
    args.output.write_text(content, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
