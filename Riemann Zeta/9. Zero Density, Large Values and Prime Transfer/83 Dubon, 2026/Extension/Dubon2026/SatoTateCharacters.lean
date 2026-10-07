import Dubon2026.SatoTateMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! # Exact symmetric-power character integrals for the actual Sato--Tate law

These are identities of the genuine angle pushforward measure. Arithmetic
prime equidistribution is not asserted here.
-/

namespace Dubon2026

open Set MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- Integrating a continuous test against the actual coefficient law is the literal weighted angle integral. -/
theorem integral_satoTateProbability {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x, g x ∂(satoTateProbability : Measure ℝ)) =
      (2 / Real.pi) * ∫ θ in 0..Real.pi, g (2 * Real.cos θ) * Real.sin θ ^ 2 := by
  change (∫ x, g x ∂Measure.map (fun θ : ℝ => 2 * Real.cos θ) satoTateAngleMeasure) = _
  rw [integral_map (show Measurable (fun θ : ℝ => 2 * Real.cos θ) by fun_prop).aemeasurable
    hg.aestronglyMeasurable, satoTateAngleMeasure,
    integral_withDensity_eq_integral_toReal_smul
      continuous_satoTateAngleDensity.measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (satoTateAngleDensity_nonneg _), smul_eq_mul,
    satoTateAngleDensity]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- Every nonconstant integer cosine mode has zero integral on the genuine angle interval. -/
theorem integral_cos_nat_mul_zero_pi {n : ℕ} (hn : n ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * θ)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hn),
    integral_cos]
  simp [Real.sin_nat_mul_pi]

/-- The literal character times the angle density reduces to the orthogonal sine product, including the endpoints. -/
theorem satoTate_character_angle_identity (n : ℕ) (θ : ℝ) :
    (Chebyshev.S ℝ (n : ℤ)).eval (2 * Real.cos θ) * Real.sin θ ^ 2 =
      Real.sin (((n : ℝ) + 1) * θ) * Real.sin θ := by
  rw [pow_two, ← mul_assoc, Chebyshev.S_two_mul_real_cos]
  norm_cast

/-- The integer cosine integral, with its exact constant mode. -/
theorem integral_cos_int_mul_zero_pi (n : ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * θ)) =
      if n = 0 then Real.pi else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, intervalIntegral.integral_comp_mul_left Real.cos
      (by exact_mod_cast hn), integral_cos]
    simp [Real.sin_int_mul_pi]

/-- Orthogonality of positive integer sine modes on the actual angle interval. -/
theorem integral_sin_nat_mul_pair (m n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)) =
        if m = n then Real.pi / 2 else 0 := by
  have he : (fun θ : ℝ => Real.sin (((m : ℝ) + 1) * θ) *
      Real.sin (((n : ℝ) + 1) * θ)) =
      (fun θ : ℝ => (Real.cos (((m : ℤ) - n : ℤ) * θ) -
        Real.cos ((((m : ℤ) + n + 2 : ℤ) : ℝ) * θ)) / 2) := by
    funext θ
    have hs := Real.cos_sub (((m : ℝ) + 1) * θ) (((n : ℝ) + 1) * θ)
    have ha := Real.cos_add (((m : ℝ) + 1) * θ) (((n : ℝ) + 1) * θ)
    push_cast
    rw [show ((m : ℝ) + 1) * θ - ((n : ℝ) + 1) * θ = ((m : ℝ) - n) * θ by ring] at hs
    rw [show ((m : ℝ) + 1) * θ + ((n : ℝ) + 1) * θ = ((m : ℝ) + n + 2) * θ by ring] at ha
    linarith
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((show Continuous (fun θ : ℝ => Real.cos (((m : ℤ) - n : ℤ) * θ)) by fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun θ : ℝ => Real.cos ((((m : ℤ) + n + 2 : ℤ) : ℝ) * θ)) by fun_prop).intervalIntegrable _ _),
    integral_cos_int_mul_zero_pi, integral_cos_int_mul_zero_pi]
  have hp : (m : ℤ) + n + 2 ≠ 0 := by omega
  simp only [hp, if_false, sub_zero]
  by_cases hmn : m = n
  · simp [hmn]
  · have hd : (m : ℤ) - n ≠ 0 := by omega
    simp [hd, hmn]

/-- The genuine Sato--Tate coefficient law makes its symmetric-power character polynomials orthonormal. -/
theorem integral_satoTate_character_pair (m n : ℕ) :
    (∫ x, (Chebyshev.S ℝ (m : ℤ)).eval x * (Chebyshev.S ℝ (n : ℤ)).eval x
      ∂(satoTateProbability : Measure ℝ)) = if m = n then 1 else 0 := by
  rw [integral_satoTateProbability (g := fun x => (Chebyshev.S ℝ (m : ℤ)).eval x *
    (Chebyshev.S ℝ (n : ℤ)).eval x)
    ((Chebyshev.S ℝ (m : ℤ)).continuous.mul (Chebyshev.S ℝ (n : ℤ)).continuous)]
  have he : (fun θ : ℝ => ((Chebyshev.S ℝ (m : ℤ)).eval (2 * Real.cos θ) *
      (Chebyshev.S ℝ (n : ℤ)).eval (2 * Real.cos θ)) * Real.sin θ ^ 2) =
      (fun θ : ℝ => Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)) := by
    funext θ
    calc
      _ = ((Chebyshev.S ℝ (m : ℤ)).eval (2 * Real.cos θ) * Real.sin θ) *
          ((Chebyshev.S ℝ (n : ℤ)).eval (2 * Real.cos θ) * Real.sin θ) := by ring
      _ = _ := by rw [Chebyshev.S_two_mul_real_cos, Chebyshev.S_two_mul_real_cos]; norm_cast
  rw [he, integral_sin_nat_mul_pair]
  split_ifs <;> simp [Real.pi_ne_zero]

/-- Every nontrivial symmetric-power character has zero mean for the actual Sato--Tate law. -/
theorem integral_satoTate_character (n : ℕ) :
    (∫ x, (Chebyshev.S ℝ (n : ℤ)).eval x ∂(satoTateProbability : Measure ℝ)) =
      if n = 0 then 1 else 0 := by
  simpa only [Nat.cast_zero, Chebyshev.S_zero, Polynomial.eval_one, one_mul, eq_comm (a := 0)]
    using integral_satoTate_character_pair 0 n

end
end Dubon2026
