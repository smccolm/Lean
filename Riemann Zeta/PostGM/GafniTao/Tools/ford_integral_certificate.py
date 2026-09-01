"""Generate exact rational certificates for Ford's Lemma 7.3 integral.

This script is a certificate generator, not proof evidence.  Its output is
intended to be checked by the Lean declarations in the isolated extension.
Only Python's exact ``Fraction`` arithmetic is used.
"""

from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import argparse


BiPoly = dict[tuple[int, int], Q]
Poly = dict[int, Q]


def write_text_if_changed(path: Path, content: str) -> None:
    """Preserve mtimes so Lake can reuse unchanged generated object files."""
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def bi_add(a: BiPoly, b: BiPoly) -> BiPoly:
    result = a.copy()
    for key, value in b.items():
        result[key] = result.get(key, Q(0)) + value
    return {key: value for key, value in result.items() if value}


def bi_scale(a: BiPoly, scalar: Q) -> BiPoly:
    return {key: value * scalar for key, value in a.items() if value * scalar}


def bi_mul(a: BiPoly, b: BiPoly) -> BiPoly:
    result: BiPoly = {}
    for (i, j), x in a.items():
        for (k, ell), y in b.items():
            key = (i + k, j + ell)
            result[key] = result.get(key, Q(0)) + x * y
    return {key: value for key, value in result.items() if value}


def bi_pow(a: BiPoly, exponent: int) -> BiPoly:
    result: BiPoly = {(0, 0): Q(1)}
    while exponent:
        if exponent & 1:
            result = bi_mul(result, a)
        if exponent > 1:
            a = bi_mul(a, a)
        exponent //= 2
    return result


def bi_integral_v(a: BiPoly) -> BiPoly:
    return {(i, j + 1): value / Q(j + 1) for (i, j), value in a.items()}


def bi_eval_v(a: BiPoly, value: Q) -> Poly:
    result: Poly = {}
    for (i, j), coefficient in a.items():
        result[i] = result.get(i, Q(0)) + coefficient * value**j
    return {degree: coefficient for degree, coefficient in result.items() if coefficient}


def bi_diagonal(a: BiPoly) -> Poly:
    result: Poly = {}
    for (i, j), coefficient in a.items():
        result[i + j] = result.get(i + j, Q(0)) + coefficient
    return {degree: coefficient for degree, coefficient in result.items() if coefficient}


def scaled_taylor(z: BiPoly, scale: int, order: int) -> BiPoly:
    negative = bi_scale(z, Q(-1, scale))
    positive = bi_scale(z, Q(1, scale))
    base: BiPoly = {}
    for k in range(order):
        base = bi_add(base, bi_scale(bi_pow(negative, k), Q(1, factorial(k))))
    remainder = Q(order + 1, factorial(order) * order)
    base = bi_add(base, bi_scale(bi_pow(positive, order), remainder))
    return bi_pow(base, scale)


def poly_add(a: Poly, b: Poly) -> Poly:
    result = a.copy()
    for degree, value in b.items():
        result[degree] = result.get(degree, Q(0)) + value
    return {degree: value for degree, value in result.items() if value}


def poly_scale(a: Poly, scalar: Q) -> Poly:
    return {degree: value * scalar for degree, value in a.items() if value * scalar}


def poly_mul(a: Poly, b: Poly) -> Poly:
    result: Poly = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i + j] = result.get(i + j, Q(0)) + x * y
    return {degree: value for degree, value in result.items() if value}


def poly_derivative(a: Poly) -> Poly:
    return {degree - 1: value * degree for degree, value in a.items() if degree}


def poly_eval(a: Poly, x: Q) -> Q:
    return sum(value * x**degree for degree, value in a.items())


def affine_substitute(a: Poly, left: Q, right: Q) -> Poly:
    width = right - left
    result: Poly = {}
    for degree, value in a.items():
        for k in range(degree + 1):
            term = value * comb(degree, k) * left ** (degree - k) * width**k
            result[k] = result.get(k, Q(0)) + term
    return {degree: value for degree, value in result.items() if value}


def bernstein_coefficients(a: Poly, left: Q, right: Q) -> list[Q]:
    transformed = affine_substitute(a, left, right)
    degree = max(transformed)
    return [
        sum(
            transformed.get(i, Q(0)) * Q(comb(k, i), comb(degree, i))
            for i in range(k + 1)
        )
        for k in range(degree + 1)
    ]


def build_polynomials() -> dict[str, BiPoly | Poly]:
    y: BiPoly = {(1, 0): Q(1)}
    v: BiPoly = {(0, 1): Q(1)}
    v2 = bi_pow(v, 2)
    negative_phase = bi_add(
        bi_scale(bi_mul(y, v2), Q(3)), bi_scale(bi_pow(v, 3), Q(-1))
    )
    positive_phase = bi_add(
        bi_scale(bi_mul(y, v2), Q(3)), bi_pow(v, 3)
    )

    negative_upper = scaled_taylor(negative_phase, 3, 6)
    positive_upper = scaled_taylor(positive_phase, 11, 6)
    negative_integral = bi_diagonal(bi_integral_v(negative_upper))
    positive_integral = bi_eval_v(bi_integral_v(positive_upper), Q(3, 2))

    tail_phase: BiPoly = {(1, 0): Q(27, 4), (0, 0): Q(27, 8)}
    tail_upper = bi_eval_v(scaled_taylor(tail_phase, 11, 8), Q(0))
    denominator: Poly = {1: Q(9), 0: Q(27, 4)}
    numerator = poly_add(
        poly_mul(denominator, poly_add(negative_integral, positive_integral)),
        tail_upper,
    )
    target = Q(108754, 100000)
    gap = poly_add(poly_scale(denominator, target), poly_scale(numerator, Q(-1)))
    derivative_numerator = poly_add(
        poly_mul(poly_derivative(numerator), denominator),
        poly_scale(poly_mul(numerator, poly_derivative(denominator)), Q(-1)),
    )
    return {
        "negative_upper": negative_upper,
        "positive_upper": positive_upper,
        "negative_primitive": bi_integral_v(negative_upper),
        "positive_primitive": bi_integral_v(positive_upper),
        "negative_diagonal": negative_integral,
        "positive_at_three_halves": positive_integral,
        "tail_at_zero": tail_upper,
        "numerator": numerator,
        "gap": gap,
        "derivative_numerator": derivative_numerator,
    }


def build_certificate() -> tuple[Poly, Poly, Poly]:
    data = build_polynomials()
    return data["numerator"], data["gap"], data["derivative_numerator"]


def positive_taylor_power_chain() -> list[Poly]:
    """Exact powers 1 through 11 of the scale-11 Taylor majorant base."""
    base: Poly = {
        k: Q((-1) ** k, 11**k * factorial(k)) for k in range(6)
    }
    base[6] = Q(7, factorial(6) * 6 * 11**6)
    powers = [base]
    for _ in range(2, 12):
        powers.append(poly_mul(powers[-1], base))
    return powers


def lean_rat(value: Q) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"({value.numerator} / {value.denominator} : ℚ)"


def lean_poly_horner(polynomial: Poly) -> str:
    degree = max(polynomial, default=0)
    expression = f"Polynomial.C {lean_rat(polynomial.get(degree, Q(0)))}"
    for index in range(degree - 1, -1, -1):
        expression = (
            f"({expression} * Polynomial.X + "
            f"Polynomial.C {lean_rat(polynomial.get(index, Q(0)))})"
        )
    return expression


def lean_bipoly_coefficients(
    prefix: str, polynomial: BiPoly
) -> tuple[list[str], list[str], str]:
    outer_degree = max((j for _, j in polynomial), default=0)
    lines: list[str] = []
    names: list[str] = []
    for j in range(outer_degree + 1):
        coefficient = {
            i: value for (i, jj), value in polynomial.items() if jj == j
        }
        name = f"{prefix}Coeff{j}"
        names.append(name)
        lines.extend(
            [
                f"abbrev {name} : Polynomial ℚ :=",
                f"  {lean_poly_horner(coefficient)}",
                "",
            ]
        )
    expression = f"Polynomial.C {names[-1]}"
    for name in reversed(names[:-1]):
        expression = f"({expression} * Polynomial.X + Polynomial.C {name})"
    return lines, names, expression


def lean_primitive_from_coefficient_names(names: list[str]) -> str:
    coefficients = ["0"] + [
        f"Polynomial.C {lean_rat(Q(1, j + 1))} * {name}"
        for j, name in enumerate(names)
    ]
    expression = f"Polynomial.C ({coefficients[-1]})"
    for coefficient in reversed(coefficients[:-1]):
        expression = (
            f"({expression} * Polynomial.X + Polynomial.C ({coefficient}))"
        )
    return expression


def lean_outer_blocks(
    prefix: str, names: list[str], primitive: bool = False
) -> tuple[list[str], str]:
    lines: list[str] = []
    block_names: list[str] = []
    for block_index, start in enumerate(range(0, len(names), 20)):
        block_name = f"{prefix}Block{block_index}"
        block_names.append(block_name)
        terms: list[str] = []
        for j, name in enumerate(names[start : start + 20], start=start):
            if primitive:
                coefficient = f"Polynomial.C {lean_rat(Q(1, j + 1))} * {name}"
                degree = j + 1
            else:
                coefficient = name
                degree = j
            terms.append(
                f"Polynomial.C ({coefficient}) * Polynomial.X ^ {degree}"
            )
        lines += [
            f"def {block_name} : FordBiPolynomial :=",
            "  " + " +\n    ".join(terms),
            "",
        ]
    return lines, " +\n    ".join(block_names)


def write_lean_primitives(path: Path) -> None:
    data = build_polynomials()
    negative_lines, negative_names, negative_upper = lean_bipoly_coefficients(
        "fordNegativeUpper", data["negative_upper"]
    )
    positive_lines, positive_names, positive_upper = lean_bipoly_coefficients(
        "fordPositiveUpper", data["positive_upper"]
    )
    negative_upper_blocks, negative_upper = lean_outer_blocks(
        "fordNegativeUpper", negative_names
    )
    positive_upper_blocks, positive_upper = lean_outer_blocks(
        "fordPositiveUpper", positive_names
    )
    negative_primitive_blocks, negative_primitive = lean_outer_blocks(
        "fordNegativePrimitive", negative_names, primitive=True
    )
    positive_primitive_blocks, positive_primitive = lean_outer_blocks(
        "fordPositivePrimitive", positive_names, primitive=True
    )
    negative_upper_block_names = [
        f"fordNegativeUpperBlock{i}" for i in range((len(negative_names) + 19) // 20)
    ]
    positive_upper_block_names = [
        f"fordPositiveUpperBlock{i}" for i in range((len(positive_names) + 19) // 20)
    ]
    data_directory = path.parent / "FordExplicitData"
    data_directory.mkdir(parents=True, exist_ok=True)
    module_names: list[str] = []

    def write_coefficient_shards(kind: str, coefficient_lines: list[str]) -> None:
        definitions_per_shard = 20
        for shard, start in enumerate(
            range(0, len(coefficient_lines), 3 * definitions_per_shard)
        ):
            module_name = f"GafniTao.FordExplicitData.{kind}{shard}"
            module_names.append(module_name)
            body = [
                "import GafniTao.FordNumericalIntegralUpper",
                "",
                "namespace GafniTao",
                "",
                "noncomputable section",
                "",
                "set_option maxRecDepth 10000000",
                "set_option maxHeartbeats 0",
                "",
            ]
            body += coefficient_lines[
                start : start + 3 * definitions_per_shard
            ]
            body += ["end", "", "end GafniTao", ""]
            write_text_if_changed(
                data_directory / f"{kind}{shard}.lean", "\n".join(body)
            )

    write_coefficient_shards("Negative", negative_lines)
    write_coefficient_shards("Positive", positive_lines)

    derived_lines = [
        *(f"import {module_name}" for module_name in module_names),
        "",
        "namespace GafniTao",
        "",
        "noncomputable section",
        "",
        "set_option maxRecDepth 100000000",
        "set_option maxHeartbeats 0",
        "",
        "",
    ]
    derived_lines += negative_upper_blocks + positive_upper_blocks
    derived_lines += negative_primitive_blocks + positive_primitive_blocks
    derived_lines += [
        "def fordNegativeUpperExplicit : FordBiPolynomial :=",
        f"  {negative_upper}",
        "",
        "def fordPositiveUpperExplicit : FordBiPolynomial :=",
        f"  {positive_upper}",
        "",
    ]
    derived_lines += [
        "def fordNegativePrimitiveExplicit : FordBiPolynomial :=",
        f"  {negative_primitive}",
        "",
        "def fordPositivePrimitiveExplicit : FordBiPolynomial :=",
        f"  {positive_primitive}",
        "",
        "end",
        "",
        "end GafniTao",
        "",
    ]
    write_text_if_changed(data_directory / "Derived.lean", "\n".join(derived_lines))

    value_modules: list[str] = []

    def write_univariate_blocks(prefix: str, polynomial: Poly) -> str:
        """Emit small coefficient/monomial blocks and return their sum."""
        degrees = list(range(max(polynomial, default=0) + 1))
        block_names: list[str] = []
        for block_index, start in enumerate(range(0, len(degrees), 12)):
            module_name = f"GafniTao.FordExplicitData.{prefix}Value{block_index}"
            value_modules.append(module_name)
            block_name = f"{prefix}ValueBlock{block_index}"
            block_names.append(block_name)
            selected = degrees[start : start + 12]
            lines = [
                "import GafniTao.FordNumericalIntegralUpper",
                "",
                "namespace GafniTao",
                "",
                "noncomputable section",
                "",
            ]
            for degree in selected:
                lines += [
                    f"abbrev {prefix}ValueCoeff{degree} : ℚ :=",
                    f"  {lean_rat(polynomial.get(degree, Q(0)))}",
                    "",
                ]
            terms = [
                f"Polynomial.C {prefix}ValueCoeff{degree} * Polynomial.X ^ {degree}"
                for degree in selected
            ]
            lines += [
                f"def {block_name} : Polynomial ℚ :=",
                "  " + " +\n    ".join(terms),
                "",
                "end",
                "",
                "end GafniTao",
                "",
            ]
            write_text_if_changed(
                data_directory / f"{prefix}Value{block_index}.lean",
                "\n".join(lines),
            )
        return " +\n    ".join(block_names)

    negative_value = write_univariate_blocks(
        "fordNegativeDiagonal", data["negative_diagonal"]
    )
    positive_value = write_univariate_blocks(
        "fordPositiveAtThreeHalves", data["positive_at_three_halves"]
    )
    tail_value = write_univariate_blocks("fordTailAtZero", data["tail_at_zero"])
    gap_value = write_univariate_blocks("fordNumericalGap", data["gap"])

    value_lines = [
        "import GafniTao.FordExplicitData.Derived",
        *(f"import {module_name}" for module_name in value_modules),
        "",
        "namespace GafniTao",
        "",
        "noncomputable section",
        "",
        "def fordNegativeDiagonalExplicit : Polynomial ℚ :=",
        f"  {negative_value}",
        "",
        "def fordPositiveAtThreeHalvesExplicit : Polynomial ℚ :=",
        f"  {positive_value}",
        "",
        "def fordTailAtZeroExplicit : Polynomial ℚ :=",
        f"  {tail_value}",
        "",
        "def fordNumericalGapExplicit : Polynomial ℚ :=",
        f"  {gap_value}",
        "",
        "end",
        "",
        "end GafniTao",
        "",
    ]
    write_text_if_changed(data_directory / "Values.lean", "\n".join(value_lines))

    gap_lines = [
        "import GafniTao.FordNumericalGap",
        "import GafniTao.FordExplicitData.Values",
        "",
        "namespace GafniTao",
        "",
        "noncomputable section",
        "",
        "def fordNumericalGapCertificate : Polynomial ℚ :=",
        "  fordNumericalGapExplicit",
        "",
        "end",
        "",
        "end GafniTao",
        "",
    ]
    write_text_if_changed(
        data_directory / "GapCertificate.lean", "\n".join(gap_lines)
    )

    positive_powers = positive_taylor_power_chain()
    for exponent, polynomial in enumerate(positive_powers, start=1):
        import_module = (
            "GafniTao.FordExplicitData.Values"
            if exponent == 1
            else f"GafniTao.FordExplicitData.PositivePower{exponent - 1}"
        )
        power_lines = [
            f"import {import_module}",
            "",
            "namespace GafniTao",
            "",
            "noncomputable section",
            "",
            "set_option maxRecDepth 100000000",
            "set_option maxHeartbeats 0",
            "",
            f"def fordPositiveTaylorPower{exponent} : Polynomial ℚ :=",
            f"  {lean_poly_horner(polynomial)}",
            "",
        ]
        if exponent > 1:
            degree = 6 * exponent
            power_lines += [
                f"theorem fordPositiveTaylorPower{exponent}_step :",
                f"    fordPositiveTaylorPower{exponent} =",
                f"      fordPositiveTaylorPower{exponent - 1} * fordPositiveTaylorPower1 := by",
                "  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq",
                f"    (f := fun i : Fin {degree + 1} => (i : ℚ))",
                "  · intro i j hij",
                "    change (i.val : ℚ) = j.val at hij",
                "    apply Fin.ext",
                "    exact_mod_cast hij",
                "  · intro i",
                "    fin_cases i <;>",
                f"      norm_num [fordPositiveTaylorPower{exponent},",
                f"        fordPositiveTaylorPower{exponent - 1}, fordPositiveTaylorPower1]",
                "  · simp only [Fintype.card_fin]",
                f"    have hleft : fordPositiveTaylorPower{exponent}.natDegree ≤ {degree} := by",
                f"      unfold fordPositiveTaylorPower{exponent}",
                "      compute_degree",
                "    have hright :",
                f"        (fordPositiveTaylorPower{exponent - 1} * fordPositiveTaylorPower1).natDegree ≤ {degree} := by",
                f"      simp only [fordPositiveTaylorPower{exponent - 1}, fordPositiveTaylorPower1]",
                "      compute_degree",
                "    omega",
                "",
            ]
        power_lines += ["end", "", "end GafniTao", ""]
        write_text_if_changed(
            data_directory / f"PositivePower{exponent}.lean", "\n".join(power_lines)
        )

    factor_lines = [
        "import GafniTao.FordExplicitData.PositivePower11",
        "",
        "namespace GafniTao",
        "",
        "noncomputable section",
        "",
        "set_option maxRecDepth 100000000",
        "set_option maxHeartbeats 0",
        "",
    ]
    factor_lines += [
        "theorem fordPositiveTaylorPower11_eq_pow :",
        "    fordPositiveTaylorPower11 = fordPositiveTaylorPower1 ^ 11 := by",
        "  rw [fordPositiveTaylorPower11_step, fordPositiveTaylorPower10_step,",
        "    fordPositiveTaylorPower9_step, fordPositiveTaylorPower8_step,",
        "    fordPositiveTaylorPower7_step, fordPositiveTaylorPower6_step,",
        "    fordPositiveTaylorPower5_step, fordPositiveTaylorPower4_step,",
        "    fordPositiveTaylorPower3_step, fordPositiveTaylorPower2_step]",
        "  ring",
        "",
        "def fordBiRatHom : ℚ →+* FordBiPolynomial :=",
        "  (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ)).comp",
        "    (Polynomial.C : ℚ →+* Polynomial ℚ)",
        "",
        "def fordPositiveLift (p : Polynomial ℚ) : FordBiPolynomial :=",
        "  Polynomial.eval₂ fordBiRatHom fordPositivePhasePolynomial p",
        "",
        "def fordPositiveUpperCompact : FordBiPolynomial :=",
        "  fordPositiveLift fordPositiveTaylorPower11",
        "",
        "theorem fordPositiveLift_mul (p q : Polynomial ℚ) :",
        "    fordPositiveLift (p * q) = fordPositiveLift p * fordPositiveLift q := by",
        "  exact map_mul",
        "    (Polynomial.eval₂RingHom fordBiRatHom fordPositivePhasePolynomial) p q",
        "",
        "theorem fordPositiveLift_pow (p : Polynomial ℚ) (n : ℕ) :",
        "    fordPositiveLift (p ^ n) = fordPositiveLift p ^ n := by",
        "  exact map_pow",
        "    (Polynomial.eval₂RingHom fordBiRatHom fordPositivePhasePolynomial) p n",
        "",
        "def fordPositiveTaylorSourceBase : Polynomial ℚ :=",
        "  (∑ k ∈ Finset.range 6,",
        "    (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k *",
        "      Polynomial.C (1 / (k.factorial : ℚ))) +",
        "    (Polynomial.C (1 / (11 : ℚ)) * Polynomial.X) ^ 6 *",
        "      Polynomial.C ((Nat.succ 6 : ℚ) / ((Nat.factorial 6 : ℚ) * 6))",
        "",
        "theorem fordPositiveTaylorPower1_eq_sourceBase :",
        "    fordPositiveTaylorPower1 = fordPositiveTaylorSourceBase := by",
        "  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq",
        "    (f := fun i : Fin 7 => (i : ℚ))",
        "  · intro i j hij",
        "    change (i.val : ℚ) = j.val at hij",
        "    apply Fin.ext",
        "    exact_mod_cast hij",
        "  · intro i",
        "    fin_cases i <;> norm_num [fordPositiveTaylorPower1,",
        "      fordPositiveTaylorSourceBase, Finset.sum_range_succ]",
        "  · simp only [Fintype.card_fin]",
        "    have hleft : fordPositiveTaylorPower1.natDegree ≤ 6 := by",
        "      unfold fordPositiveTaylorPower1",
        "      compute_degree",
        "    have hright : fordPositiveTaylorSourceBase.natDegree ≤ 6 := by",
        "      unfold fordPositiveTaylorSourceBase",
        "      apply le_trans (Polynomial.natDegree_add_le _ _)",
        "      apply max_le",
        "      · apply Polynomial.natDegree_sum_le_of_forall_le",
        "        intro k hk",
        "        have hk6 : k ≤ 6 := (Finset.mem_range.mp hk).le",
        "        calc",
        "          ((Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k *",
        "              Polynomial.C (1 / (k.factorial : ℚ))).natDegree",
        "              ≤ ((Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X) ^ k).natDegree +",
        "                  (Polynomial.C (1 / (k.factorial : ℚ))).natDegree :=",
        "                Polynomial.natDegree_mul_le",
        "          _ ≤ k * (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X).natDegree + 0 := by",
        "                gcongr",
        "                · exact Polynomial.natDegree_pow_le",
        "                · exact Mathlib.Tactic.ComputeDegree.natDegree_C_le _",
        "          _ ≤ k := by",
        "                have hb : (Polynomial.C (-1 / (11 : ℚ)) * Polynomial.X).natDegree = 1 := by",
        "                  compute_degree; norm_num",
        "                rw [hb]",
        "                simp",
        "          _ ≤ 6 := hk6",
        "      · compute_degree",
        "    omega",
        "",
        "theorem fordPositiveLift_base :",
        "    fordPositiveLift fordPositiveTaylorPower1 =",
        "      (∑ k ∈ Finset.range 6,",
        "        (fordBiRat (-1 / (11 : ℚ)) * fordPositivePhasePolynomial) ^ k *",
        "          fordBiRat (1 / (k.factorial : ℚ))) +",
        "        (fordBiRat (1 / (11 : ℚ)) * fordPositivePhasePolynomial) ^ 6 *",
        "          fordBiRat ((Nat.succ 6 : ℚ) / ((Nat.factorial 6 : ℚ) * 6)) := by",
        "  rw [fordPositiveTaylorPower1_eq_sourceBase]",
        "  unfold fordPositiveLift fordPositiveTaylorSourceBase",
        "  rw [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum]",
        "  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,",
        "    Polynomial.eval₂_C, Polynomial.eval₂_X]",
        "  rfl",
        "",
        "theorem fordPositiveUpperPolynomial_eq_compact :",
        "    fordPositiveUpperPolynomial = fordPositiveUpperCompact := by",
        "  unfold fordPositiveUpperPolynomial fordScaledTaylorPolynomial",
        "  unfold fordPositiveUpperCompact",
        "  rw [fordPositiveTaylorPower11_eq_pow, fordPositiveLift_pow,",
        "    fordPositiveLift_base]",
        "  norm_num",
        "",
        "end",
        "",
        "end GafniTao",
        "",
    ]
    write_text_if_changed(
        data_directory / "PositiveFactor.lean", "\n".join(factor_lines)
    )

    wrapper = [
        "import GafniTao.FordExplicitData.PositiveFactor",
        "",
        "/-!",
        "# Explicit exact polynomial certificates",
        "",
        "The exact rational data are sharded into small modules so that Lean can",
        "kernel-check and cache each block.  No generated coefficient is trusted:",
        "the source-identification theorems are proved in the consumer module.",
        "-/",
        "",
        "namespace GafniTao",
        "",
        "noncomputable section",
        "",
        "set_option maxRecDepth 100000000",
        "",
        "set_option maxHeartbeats 0 in",
        "theorem fordNegativeUpperPolynomial_eq_explicit :",
        "    fordNegativeUpperPolynomial = fordNegativeUpperExplicit := by",
        "  apply Polynomial.funext",
        "  intro v",
        "  apply Polynomial.funext",
        "  intro y",
        "  norm_num [fordNegativeUpperPolynomial, fordScaledTaylorPolynomial,",
        "    fordNegativePhasePolynomial, fordBiRat, fordBiY, fordBiV,",
        "    fordNegativeUpperExplicit, Finset.sum_range_succ,",
        "    " + ", ".join(negative_upper_block_names + negative_names) + "]",
        "  ring",
        "",
        "end",
        "",
        "end GafniTao",
        "",
    ]
    write_text_if_changed(path, "\n".join(wrapper))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()
    if args.lean_output is not None:
        write_lean_primitives(args.lean_output)
        return
    numerator, gap, derivative_numerator = build_certificate()
    denominator = {1: Q(9), 0: Q(27, 4)}
    center = Q(71, 100)
    print(f"numerator degree: {max(numerator)}")
    print(f"gap degree: {max(gap)}")
    print(
        "upper value at 0.71:",
        float(poly_eval(numerator, center) / poly_eval(denominator, center)),
    )
    print("gap numerator at 0.71:", float(poly_eval(gap, center)))

    for pieces in (1, 2, 4, 8, 16, 32, 64, 128):
        bad = 0
        minimum: Q | None = None
        for index in range(pieces):
            left = Q(11, 10) * Q(index, pieces)
            right = Q(11, 10) * Q(index + 1, pieces)
            coefficients = bernstein_coefficients(gap, left, right)
            local_minimum = min(coefficients)
            minimum = local_minimum if minimum is None else min(minimum, local_minimum)
            if local_minimum < 0:
                bad += 1
        print(
            f"gap subdivision {pieces:3d}: bad={bad:3d}, "
            f"minimum={float(minimum):.12g}"
        )
        if bad == 0:
            break

    # These derivative diagnostics are useful when a smaller monotonicity
    # certificate is preferable to a direct gap certificate.
    for name, left, right, polynomial in (
        ("left derivative", Q(1, 100), Q(71, 100), derivative_numerator),
        (
            "right negative derivative",
            Q(711, 1000),
            Q(11, 10),
            poly_scale(derivative_numerator, Q(-1)),
        ),
    ):
        for pieces in (1, 2, 4, 8, 16, 32, 64):
            bad = 0
            minimum: Q | None = None
            for index in range(pieces):
                a = left + (right - left) * Q(index, pieces)
                b = left + (right - left) * Q(index + 1, pieces)
                coefficients = bernstein_coefficients(polynomial, a, b)
                local_minimum = min(coefficients)
                minimum = local_minimum if minimum is None else min(minimum, local_minimum)
                if local_minimum < 0:
                    bad += 1
            print(
                f"{name} subdivision {pieces:3d}: bad={bad:3d}, "
                f"minimum={float(minimum):.12g}"
            )
            if bad == 0:
                break


if __name__ == "__main__":
    main()
