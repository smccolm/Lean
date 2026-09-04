import GafniTao.WooleyWeightedComplexHolder
import GafniTao.WooleyWeightedMean

/-!
# Wooley equations (3.9) and (3.10)

This file assembles the exact residue decomposition and the weighted finite
Hölder estimate.  The result is the source normalization with one inverse
global `L²` mass, rather than an unspecified constant.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_sqrt_inverse_power_mul
    {M : ℝ} {s : ℕ} (hM : 0 < M) (hs : 1 ≤ s) :
    (Real.sqrt M)⁻¹ ^ (2 * s) * M ^ (s - 1) = M⁻¹ := by
  have hsqrt : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  have hpow : M ^ s = M ^ (s - 1) * M := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_add, pow_one]
  rw [pow_mul, inv_pow, Real.sq_sqrt hM.le]
  rw [inv_pow, hpow]
  field_simp

/-- Equation (3.9), on the literal finite residue grid. -/
theorem wooley_equation_3_9
    {Q qB qH k s : ℕ} [NeZero qB] [NeZero qH]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (hs : 1 ≤ s) (hmass : wooleyWeightedMassSq gamma ≠ 0) :
    ‖wooleyWeightedNormalizedGridSum qB k gamma alpha‖ ^ (2 * s) ≤
      (qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
        ∑ xi : ZMod qH,
          wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha xi‖ ^ (2 * s) := by
  let M := wooleyWeightedMassSq gamma
  let S : ℂ := ∑ xi : ZMod qH,
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
      wooleyWeightedNormalizedResidueGridSum qB k gamma alpha xi
  let R : ℝ := ∑ xi : ZMod qH,
    wooleyWeightedResidueMassSq gamma xi *
      ‖wooleyWeightedNormalizedResidueGridSum qB k gamma alpha xi‖ ^ (2 * s)
  have hM : 0 < M := lt_of_le_of_ne
    (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
  have hdecomp := wooley_weighted_normalizedGridSum_decomposition
    (qH := qH) gamma alpha hmass
  have hholder := wooley_weighted_complex_sum_pow_le
    (Finset.univ : Finset (ZMod qH))
    (fun xi => wooleyWeightedResidueMassSq gamma xi)
    (fun xi => wooleyWeightedNormalizedResidueGridSum
      qB k gamma alpha xi) hs
    (fun xi => wooleyWeightedResidueMassSq_nonneg gamma xi)
  have hholder' : ‖S‖ ^ (2 * s) ≤
      (qH : ℝ) ^ s * M ^ (s - 1) * R := by
    simpa only [S, R, Finset.card_univ, ZMod.card,
      wooley_sum_weightedResidueMassSq] using hholder
  rw [hdecomp]
  have hsqrtNorm : ‖((Real.sqrt M : ℝ) : ℂ)⁻¹‖ = (Real.sqrt M)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hsqrtNorm, mul_pow]
  calc
    (Real.sqrt M)⁻¹ ^ (2 * s) * ‖S‖ ^ (2 * s) ≤
        (Real.sqrt M)⁻¹ ^ (2 * s) *
          ((qH : ℝ) ^ s * M ^ (s - 1) * R) := by
      gcongr
    _ = (qH : ℝ) ^ s * M⁻¹ * R := by
      calc
        (Real.sqrt M)⁻¹ ^ (2 * s) *
            ((qH : ℝ) ^ s * M ^ (s - 1) * R) =
            (qH : ℝ) ^ s *
              ((Real.sqrt M)⁻¹ ^ (2 * s) * M ^ (s - 1)) * R := by ring
        _ = (qH : ℝ) ^ s * M⁻¹ * R := by
          rw [wooley_sqrt_inverse_power_mul hM hs]
    _ = _ := by rfl

/-- Equation (3.10), obtained by averaging (3.9) over the complete
coefficient grid. -/
theorem wooley_equation_3_10
    {Q qB qH k s : ℕ} [NeZero qB] [NeZero qH]
    (gamma : Fin Q → ℂ) (hs : 1 ≤ s) :
    wooleyWeightedGridMean s k qB gamma ≤
      (qH : ℝ) ^ s *
        wooleyWeightedConditionedGridMean s k qB qH gamma := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyWeightedGridMean, wooleyWeightedConditionedGridMean,
      wooleyWeightedNormalizedGridSum, hmass, hs0]
  · have hpoint (alpha : Fin k → ZMod qB) :=
      wooley_equation_3_9 (qH := qH) gamma alpha hs hmass
    have hsum :
        ∑ alpha : Fin k → ZMod qB,
            ‖wooleyWeightedNormalizedGridSum qB k gamma alpha‖ ^ (2 * s) ≤
          ∑ alpha : Fin k → ZMod qB,
            (qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
              ∑ xi : ZMod qH,
                wooleyWeightedResidueMassSq gamma xi *
                  ‖wooleyWeightedNormalizedResidueGridSum
                      qB k gamma alpha xi‖ ^ (2 * s) :=
      Finset.sum_le_sum fun alpha _ => hpoint alpha
    unfold wooleyWeightedGridMean wooleyWeightedConditionedGridMean
    rw [if_neg hmass]
    calc
      (((qB ^ k : ℕ) : ℝ))⁻¹ *
          ∑ alpha : Fin k → ZMod qB,
            ‖wooleyWeightedNormalizedGridSum qB k gamma alpha‖ ^ (2 * s) ≤
          (((qB ^ k : ℕ) : ℝ))⁻¹ *
            ∑ alpha : Fin k → ZMod qB,
              (qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
                ∑ xi : ZMod qH,
                  wooleyWeightedResidueMassSq gamma xi *
                    ‖wooleyWeightedNormalizedResidueGridSum
                        qB k gamma alpha xi‖ ^ (2 * s) := by
        gcongr
      _ = (qH : ℝ) ^ s *
          ((wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod qH,
              wooleyWeightedResidueMassSq gamma xi *
                ((((qB ^ k : ℕ) : ℝ))⁻¹ *
                  ∑ alpha : Fin k → ZMod qB,
                    ‖wooleyWeightedNormalizedResidueGridSum
                        qB k gamma alpha xi‖ ^ (2 * s))) := by
        calc
          (((qB ^ k : ℕ) : ℝ))⁻¹ *
              ∑ alpha : Fin k → ZMod qB,
                (qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
                  ∑ xi : ZMod qH,
                    wooleyWeightedResidueMassSq gamma xi *
                      ‖wooleyWeightedNormalizedResidueGridSum
                          qB k gamma alpha xi‖ ^ (2 * s) =
              (((qB ^ k : ℕ) : ℝ))⁻¹ *
                ∑ alpha : Fin k → ZMod qB,
                  ∑ xi : ZMod qH,
                    ((qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹) *
                      (wooleyWeightedResidueMassSq gamma xi *
                        ‖wooleyWeightedNormalizedResidueGridSum
                            qB k gamma alpha xi‖ ^ (2 * s)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro alpha halpha
            rw [Finset.mul_sum]
          _ = (((qB ^ k : ℕ) : ℝ))⁻¹ *
                ∑ xi : ZMod qH,
                  ∑ alpha : Fin k → ZMod qB,
                    ((qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹) *
                      (wooleyWeightedResidueMassSq gamma xi *
                        ‖wooleyWeightedNormalizedResidueGridSum
                            qB k gamma alpha xi‖ ^ (2 * s)) := by
            rw [Finset.sum_comm]
          _ = (qH : ℝ) ^ s *
              ((wooleyWeightedMassSq gamma)⁻¹ *
                ∑ xi : ZMod qH,
                  wooleyWeightedResidueMassSq gamma xi *
                    ((((qB ^ k : ℕ) : ℝ))⁻¹ *
                      ∑ alpha : Fin k → ZMod qB,
                        ‖wooleyWeightedNormalizedResidueGridSum
                            qB k gamma alpha xi‖ ^ (2 * s))) := by
            rw [show
              (∑ xi : ZMod qH,
                  wooleyWeightedResidueMassSq gamma xi *
                    ((((qB ^ k : ℕ) : ℝ))⁻¹ *
                      ∑ alpha : Fin k → ZMod qB,
                        ‖wooleyWeightedNormalizedResidueGridSum
                            qB k gamma alpha xi‖ ^ (2 * s))) =
                (((qB ^ k : ℕ) : ℝ))⁻¹ *
                  ∑ xi : ZMod qH,
                    wooleyWeightedResidueMassSq gamma xi *
                      ∑ alpha : Fin k → ZMod qB,
                        ‖wooleyWeightedNormalizedResidueGridSum
                            qB k gamma alpha xi‖ ^ (2 * s) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro xi hxi
              ring]
            simp_rw [← Finset.mul_sum]
            ring_nf

#print axioms wooley_sqrt_inverse_power_mul
#print axioms wooley_equation_3_9
#print axioms wooley_equation_3_10

end

end GafniTao
