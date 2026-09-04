import GafniTao.WooleyPolynomialBasic
import GafniTao.WooleyResidueRefinement

/-!
# Residue refinement for polynomial systems

The residue-class argument in Wooley Lemma 6.2 is independent of the
particular polynomial phase.  This file proves it for the `p^c`-spaced
systems used by the induction in Section 7.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyPolynomial_sum_refined_residue_grid
    {Q p a b qB k : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha z =
      wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha xi := by
  unfold wooleyPolynomialWeightedResidueGridSum wooleyResidueClass
    wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n : Fin Q,
            if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyPolynomialGridPhase phi qB Q alpha n else 0
        else 0) =
        ∑ n : Fin Q,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyPolynomialGridPhase phi qB Q alpha n else 0)
          else 0 := by
    by_cases hz : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi <;> simp [hz]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Fintype.sum_eq_single
    (((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))]
  · have hcast :
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
            ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) =
          ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) :=
      ZMod.cast_natCast (pow_dvd_pow p hab) ((n : ℕ) + 1)
    rw [hcast]
    by_cases hxi : ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) = xi <;>
      simp [hxi]
  · intro z hzne
    by_cases hzxi : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi
    · rw [if_pos hzxi, if_neg (Ne.symm hzne)]
    · rw [if_neg hzxi]

theorem wooleyPolynomial_refined_normalized_residue_decomposition
    {Q p a b qB k : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha xi =
      ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        (Real.sqrt (wooleyWeightedResidueMassSq gamma z) : ℂ) *
          wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha z := by
  rw [wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    phi gamma alpha]
  simp_rw [wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    phi gamma alpha]
  exact (wooleyPolynomial_sum_refined_residue_grid
    phi hab gamma alpha xi).symm

/-- Polynomial-system form of Wooley Lemma 6.2. -/
theorem wooleyPolynomial_lemma_6_2
    {Q p a b qB k w : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b) (hw : 1 ≤ w)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    wooleyWeightedResidueMassSq gamma xi *
        ‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha xi‖ ^ (2 * w) ≤
      (p ^ (b - a) : ℝ) ^ w *
        ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
          wooleyWeightedResidueMassSq gamma z *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha z‖ ^ (2 * w) := by
  let M := wooleyWeightedResidueMassSq gamma xi
  let R : ℝ :=
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
      wooleyWeightedResidueMassSq gamma z *
        ‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha z‖ ^ (2 * w)
  by_cases hMzero : M = 0
  · have hR : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg fun z hz => mul_nonneg
        (wooleyWeightedResidueMassSq_nonneg gamma z) (by positivity)
    dsimp [M] at hMzero
    rw [hMzero, zero_mul]
    exact mul_nonneg (by positivity) hR
  · have hMpos : 0 < M := lt_of_le_of_ne
      (wooleyWeightedResidueMassSq_nonneg gamma xi) (Ne.symm hMzero)
    have hholder := wooley_weighted_complex_sum_pow_le
      (wooleyResidueRefinementFiber p a b hab xi)
      (fun z => wooleyWeightedResidueMassSq gamma z)
      (fun z => wooleyPolynomialNormalizedResidueGridSum
        phi qB gamma alpha z) hw
      (fun z => wooleyWeightedResidueMassSq_nonneg gamma z)
    have hdecomp :=
      wooleyPolynomial_refined_normalized_residue_decomposition
        phi hab gamma alpha xi
    have hsource :
        M ^ w *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha xi‖ ^ (2 * w) ≤
          (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := by
      rw [← hdecomp] at hholder
      simpa only [M, R, wooleyResidueRefinementFiber_card hab xi,
        wooley_sum_refined_residue_mass hab gamma xi,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, pow_mul,
        Real.sq_sqrt hMpos.le, Nat.cast_pow] using hholder
    have hpow : M ^ w = M ^ (w - 1) * M := by
      conv_lhs => rw [← Nat.sub_add_cancel hw, pow_add, pow_one]
    have hfactorPos : 0 < M ^ (w - 1) := pow_pos hMpos _
    have hfactored :
        M ^ (w - 1) *
            (M * ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi‖ ^ (2 * w)) ≤
          M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by
      rw [← mul_assoc, ← hpow]
      calc
        M ^ w *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha xi‖ ^ (2 * w) ≤
            (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := hsource
        _ = M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by ring
    exact le_of_mul_le_mul_left hfactored hfactorPos

#print axioms wooleyPolynomial_sum_refined_residue_grid
#print axioms wooleyPolynomial_refined_normalized_residue_decomposition
#print axioms wooleyPolynomial_lemma_6_2

end

end GafniTao
