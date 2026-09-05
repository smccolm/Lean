import GafniTao.Pintz2023LargeMInnerBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Pintz equation (4.14): summing the Möbius factor

The inner Corollary-3 estimate is summed over the literal range `1 ≤ d ≤ X`.
The factor `d^{-rho*}` is retained, yielding the source's harmonic-times-
`X^xi` loss rather than the much weaker cardinality loss `X`.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz2023LargeMFactorizedBlock_eq_sum_Icc
    {X A B : ℕ} {Q xi t : ℝ} (hXB : X ≤ B + 1) :
    pintz2023LargeMFactorizedBlock X B (Finset.Ioc A B) Q
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) =
      ∑ d ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (d : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ))) *
          pintz2023LargeMInnerBlock B d (Finset.Ioc A B) Q
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) := by
  classical
  unfold pintz2023LargeMFactorizedBlock
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 (B + 1)).filter (fun d => d ≤ X) =
        Finset.Icc 1 X := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter]

theorem sum_Icc_rpow_sub_one_le_rpow_mul_harmonic
    {X : ℕ} {xi : ℝ} (hxi : 0 ≤ xi) :
    ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ^ (xi - 1) ≤
      (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) := by
  calc
    ∑ d ∈ Finset.Icc 1 X, (d : ℝ) ^ (xi - 1) ≤
        ∑ d ∈ Finset.Icc 1 X,
          (X : ℝ) ^ xi * (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdData := Finset.mem_Icc.mp hd
      have hdPos : (0 : ℝ) < d := by exact_mod_cast hdData.1
      have hdX : (d : ℝ) ≤ X := by exact_mod_cast hdData.2
      have hpow : (d : ℝ) ^ xi ≤ (X : ℝ) ^ xi :=
        Real.rpow_le_rpow hdPos.le hdX hxi
      calc
        (d : ℝ) ^ (xi - 1) =
            (d : ℝ) ^ xi * (d : ℝ) ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hdPos]
          congr 1
        _ = (d : ℝ) ^ xi * (d : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
        _ ≤ (X : ℝ) ^ xi * (d : ℝ)⁻¹ := by gcongr
    _ = (X : ℝ) ^ xi *
        (∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ = (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]

theorem pintz2023LargeMFactorizedBlock_corollary_three
    (r : ℕ) (epsilon B₀ : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (xi Q t T : ℝ) (X A B : ℕ),
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi -
          6 * (r : ℝ) * epsilon →
        0 ≤ xi → xi + 3 * epsilon ≤ 1 →
        1 ≤ Q →
        pintz2023CriticalScale r xi epsilon T ≤ Q →
        0 < |t| → |t| ≤ T → 1 ≤ T →
        1 ≤ X → X ≤ A → A ≤ B + 1 → B ≤ 2 * A →
        (∀ d : ℕ, 0 < d → d ≤ X →
          ((max (A / d) (Nat.ceil Q) : ℕ) : ℝ) ≤
            B₀ * |t| ^ (2 / (r : ℝ))) →
        ‖pintz2023LargeMFactorizedBlock X B (Finset.Ioc A B) Q
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          C * (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) *
            Q ^ (-3 * epsilon) := by
  obtain ⟨C, hC, hinner⟩ :=
    pintz2023LargeMInnerBlock_corollary_three
      r epsilon B₀ hr hepsilon hB₀
  refine ⟨C, hC, ?_⟩
  intro xi Q t T X A B hxiAlpha hden hxi hxiOne hQ hcritical
    ht htT hT hX hXA hAB hBA hphysical
  have hXB : X ≤ B + 1 := hXA.trans hAB
  rw [pintz2023LargeMFactorizedBlock_eq_sum_Icc hXB]
  calc
    ‖∑ d ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (d : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ))) *
          pintz2023LargeMInnerBlock B d (Finset.Ioc A B) Q
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
        ∑ d ∈ Finset.Icc 1 X,
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (d : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ))) *
            pintz2023LargeMInnerBlock B d (Finset.Ioc A B) Q
              (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 X,
        (d : ℝ) ^ (xi - 1) * (C * Q ^ (-3 * epsilon)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdData := Finset.mem_Icc.mp hd
      have hdPos : 0 < d := hdData.1
      have hdA : d ≤ A := hdData.2.trans hXA
      have hInner := hinner xi Q t T A B d hxiAlpha hden hxiOne hQ
        hcritical ht htT hT hdPos hdA hBA (hphysical d hdPos hdData.2)
      have hdReal : (0 : ℝ) < d := by exact_mod_cast hdPos
      have hPower :
          ‖(d : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)))‖ =
            (d : ℝ) ^ (xi - 1) :=
        norm_pintz2023_complex_weighted_term hdPos xi t
      rw [norm_mul, norm_mul, hPower]
      have hMu : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 :=
        by simpa using moebius_coeff_norm_le_one d
      calc
        ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ *
            (d : ℝ) ^ (xi - 1) *
              ‖pintz2023LargeMInnerBlock B d (Finset.Ioc A B) Q
                (↑(1 - xi) + I * ↑t)‖ ≤
            1 * (d : ℝ) ^ (xi - 1) * (C * Q ^ (-3 * epsilon)) := by
          gcongr
        _ = (d : ℝ) ^ (xi - 1) * (C * Q ^ (-3 * epsilon)) := by ring
    _ = (∑ d ∈ Finset.Icc 1 X, (d : ℝ) ^ (xi - 1)) *
          (C * Q ^ (-3 * epsilon)) := by rw [Finset.sum_mul]
    _ ≤ ((X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ)) *
          (C * Q ^ (-3 * epsilon)) := by
      gcongr
      exact sum_Icc_rpow_sub_one_le_rpow_mul_harmonic hxi
    _ = C * (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) *
          Q ^ (-3 * epsilon) := by ring

#print axioms pintz2023LargeMFactorizedBlock_eq_sum_Icc
#print axioms sum_Icc_rpow_sub_one_le_rpow_mul_harmonic
#print axioms pintz2023LargeMFactorizedBlock_corollary_three

end

end GafniTao
