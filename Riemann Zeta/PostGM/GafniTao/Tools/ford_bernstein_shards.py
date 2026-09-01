"""Generate the bounded-size Ford affine/Bernstein certificate shards.

Run this after ``ford_integral_certificate.py --lean-output ...``.  It replaces
the dense per-interval polynomial identity with generic Hasse/Bernstein basis
theorems plus exact rational coefficient checks.
"""

from fractions import Fraction as Q
from pathlib import Path

from ford_integral_certificate import (
    affine_substitute,
    bernstein_coefficients,
    build_polynomials,
    lean_rat,
    write_text_if_changed,
)


def generate(extension: Path) -> None:
    data = build_polynomials()
    data_directory = extension / "GafniTao" / "FordExplicitData"
    affine_directory = data_directory / "Affine"
    bernstein_directory = data_directory / "Bernstein"
    affine_directory.mkdir(parents=True, exist_ok=True)
    bernstein_directory.mkdir(parents=True, exist_ok=True)

    for interval in range(8):
        left = Q(11 * interval, 80)
        right = Q(11 * (interval + 1), 80)
        affine_coefficients = affine_substitute(data["gap"], left, right)
        bernstein_coeffs = bernstein_coefficients(data["gap"], left, right)

        affine_data = [
            "import GafniTao.FordBernsteinBasis",
            "import GafniTao.FordGapDegree",
            "",
            "namespace GafniTao",
            "",
            "noncomputable section",
            "",
            "set_option maxRecDepth 100000000",
            "set_option maxHeartbeats 0",
            "",
            f"def fordGapAffineSource{interval} : Polynomial ℚ :=",
            "  fordNumericalGapExplicit.comp",
            f"    (Polynomial.C {lean_rat(left)} +",
            "      Polynomial.C (11 / 80 : ℚ) * Polynomial.X)",
            "",
            f"def fordGapAffineCoeff{interval} : ℕ → ℚ",
        ]
        for degree in range(89):
            affine_data.append(
                f"  | {degree} => "
                f"{lean_rat(affine_coefficients.get(degree, Q(0)))}"
            )
        affine_data += [
            "  | _ => 0",
            "",
            f"theorem fordGapAffineSource{interval}_natDegree_le :",
            f"    fordGapAffineSource{interval}.natDegree ≤ 88 := by",
            f"  unfold fordGapAffineSource{interval}",
            "  refine Polynomial.natDegree_comp_le.trans ?_",
            "  have ha :",
            f"      (Polynomial.C {lean_rat(left)} +",
            "        Polynomial.C (11 / 80 : ℚ) * Polynomial.X).natDegree ≤ 1 := by",
            "    compute_degree",
            "  exact (Nat.mul_le_mul fordNumericalGapExplicit_natDegree_le ha).trans_eq",
            "    (by norm_num)",
            "",
            "end",
            "",
            "end GafniTao",
            "",
        ]
        write_text_if_changed(
            affine_directory / f"Interval{interval}Data.lean",
            "\n".join(affine_data),
        )

        affine_modules: list[str] = []
        for shard, start in enumerate(range(0, 89, 8)):
            selected = range(start, min(start + 8, 89))
            module_name = (
                "GafniTao.FordExplicitData.Affine."
                f"Interval{interval}Coeff{shard}"
            )
            affine_modules.append(module_name)
            lines = [
                f"import GafniTao.FordExplicitData.Affine.Interval{interval}Data",
                "",
                "namespace GafniTao",
                "",
                "noncomputable section",
                "",
                "set_option maxRecDepth 100000000",
                "set_option maxHeartbeats 0",
                "",
            ]
            for degree in selected:
                lines += [
                    "@[simp] theorem "
                    f"fordGapAffineSource{interval}_coeff_{degree} :",
                    f"    fordGapAffineSource{interval}.coeff {degree} =",
                    f"      fordGapAffineCoeff{interval} {degree} := by",
                    f"  unfold fordGapAffineSource{interval}",
                    "  rw [coeff_comp_affine,",
                    "    hasseDeriv_eval_eq_sum_range 88 "
                    f"{degree} fordNumericalGapExplicit {lean_rat(left)}",
                    "      fordNumericalGapExplicit_natDegree_le]",
                    "  norm_num [Finset.sum_range_succ, Nat.choose,",
                    f"    fordGapAffineCoeff{interval}]",
                    "",
                ]
            lines += ["end", "", "end GafniTao", ""]
            write_text_if_changed(
                affine_directory / f"Interval{interval}Coeff{shard}.lean",
                "\n".join(lines),
            )

        write_text_if_changed(
            affine_directory / f"Interval{interval}.lean",
            "\n".join([*(f"import {m}" for m in affine_modules), ""]),
        )

        bernstein_data = [
            f"import GafniTao.FordExplicitData.Affine.Interval{interval}",
            "",
            "namespace GafniTao",
            "",
            "noncomputable section",
            "",
            "set_option maxRecDepth 100000000",
            "set_option maxHeartbeats 0",
            "",
            f"def fordGapBernsteinCoeff{interval} : ℕ → ℚ",
        ]
        for k, coefficient in enumerate(bernstein_coeffs):
            bernstein_data.append(f"  | {k} => {lean_rat(coefficient)}")
        bernstein_data += [
            "  | _ => 0",
            "",
            f"def fordGapBernsteinExpansion{interval} : Polynomial ℚ :=",
            "  ∑ k ∈ Finset.range 89,",
            f"    Polynomial.C (fordGapBernsteinCoeff{interval} k) *",
            "      bernsteinPolynomial ℚ 88 k",
            "",
            f"theorem fordGapBernsteinCoeff{interval}_nonneg",
            f"    {{k : ℕ}} (hk : k < 89) : 0 ≤ fordGapBernsteinCoeff{interval} k := by",
            "  interval_cases k <;>",
            f"    norm_num [fordGapBernsteinCoeff{interval}]",
            "",
            "end",
            "",
            "end GafniTao",
            "",
        ]
        write_text_if_changed(
            bernstein_directory / f"Interval{interval}Data.lean",
            "\n".join(bernstein_data),
        )

        bernstein_modules: list[str] = []
        for shard, start in enumerate(range(0, 89, 8)):
            selected = range(start, min(start + 8, 89))
            module_name = (
                "GafniTao.FordExplicitData.Bernstein."
                f"Interval{interval}Coeff{shard}"
            )
            bernstein_modules.append(module_name)
            lines = [
                f"import GafniTao.FordExplicitData.Bernstein.Interval{interval}Data",
                "",
                "namespace GafniTao",
                "",
                "noncomputable section",
                "",
                "set_option maxRecDepth 100000000",
                "set_option maxHeartbeats 0",
                "",
            ]
            for k in selected:
                lines += [
                    "@[simp] theorem "
                    f"fordGapBernsteinSourceCoeff{interval}_{k} :",
                    f"    polynomialBernsteinCoeff 88 fordGapAffineSource{interval} {k} =",
                    f"      fordGapBernsteinCoeff{interval} {k} := by",
                    "  norm_num [polynomialBernsteinCoeff, powerBernsteinCoeff,",
                    "    Finset.sum_range_succ, Nat.choose,",
                    f"    fordGapAffineCoeff{interval}, fordGapBernsteinCoeff{interval}]",
                    "",
                ]
            lines += ["end", "", "end GafniTao", ""]
            write_text_if_changed(
                bernstein_directory / f"Interval{interval}Coeff{shard}.lean",
                "\n".join(lines),
            )

        interval_file = [
            *(f"import {m}" for m in bernstein_modules),
            "",
            "namespace GafniTao",
            "",
            "noncomputable section",
            "",
            f"theorem fordGapBernsteinSourceCoeff{interval}",
            f"    {{k : ℕ}} (hk : k < 89) :",
            f"    polynomialBernsteinCoeff 88 fordGapAffineSource{interval} k =",
            f"      fordGapBernsteinCoeff{interval} k := by",
            "  interval_cases k <;> simp",
            "",
            f"theorem fordGapAffine{interval}_eq_bernstein :",
            f"    fordGapAffineSource{interval} = fordGapBernsteinExpansion{interval} := by",
            "  rw [polynomial_eq_bernsteinExpansion 88",
            f"    fordGapAffineSource{interval} fordGapAffineSource{interval}_natDegree_le]",
            "  unfold polynomialBernsteinExpansion",
            f"  unfold fordGapBernsteinExpansion{interval}",
            "  apply Finset.sum_congr rfl",
            "  intro k hk",
            f"  rw [fordGapBernsteinSourceCoeff{interval} (Finset.mem_range.mp hk)]",
            "",
            "end",
            "",
            "end GafniTao",
            "",
        ]
        write_text_if_changed(
            bernstein_directory / f"Interval{interval}.lean",
            "\n".join(interval_file),
        )

    write_text_if_changed(
        data_directory / "BernsteinIntervals.lean",
        "\n".join(
            [
                *(
                    f"import GafniTao.FordExplicitData.Bernstein.Interval{i}"
                    for i in range(8)
                ),
                "",
            ]
        ),
    )


if __name__ == "__main__":
    generate(Path(__file__).resolve().parents[1] / "Extension")
