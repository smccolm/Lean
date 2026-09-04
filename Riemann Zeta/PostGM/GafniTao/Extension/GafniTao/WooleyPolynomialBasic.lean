import GafniTao.WooleyPolynomialSystem
import GafniTao.WooleyEquation39

/-!
# Basic identities for Wooley polynomial systems

These are the polynomial-system versions of the residue decomposition and
equations (3.9)--(3.10).  Their proofs do not use the monomial shape; that
shape enters only in the congruence extraction of Section 7.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyPolynomialResidueGridSum_eq_zero_of_massSq_eq_zero
    {Q k qH qB : ℕ} (phi : WooleyPolynomialSystem k) [NeZero qB]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB) (xi : ZMod qH)
    (hmass : wooleyWeightedResidueMassSq gamma xi = 0) :
    wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha xi = 0 := by
  have hterm : ∀ n ∈ wooleyResidueClass Q qH xi, ‖gamma n‖ ^ 2 = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp
    simpa [wooleyWeightedResidueMassSq] using hmass
  unfold wooleyPolynomialWeightedResidueGridSum
  apply Finset.sum_eq_zero
  intro n hn
  have hnzero : ‖gamma n‖ = 0 := (sq_eq_zero_iff).mp (hterm n hn)
  rw [norm_eq_zero] at hnzero
  simp [hnzero]

theorem wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    {Q k qH qB : ℕ} (phi : WooleyPolynomialSystem k) [NeZero qB]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB) (xi : ZMod qH) :
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha xi =
      wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha xi := by
  by_cases hmass : wooleyWeightedResidueMassSq gamma xi = 0
  · simp [wooleyPolynomialNormalizedResidueGridSum, hmass,
      wooleyPolynomialResidueGridSum_eq_zero_of_massSq_eq_zero
        phi gamma alpha xi hmass]
  · have hmassPos : 0 < wooleyWeightedResidueMassSq gamma xi :=
      lt_of_le_of_ne (wooleyWeightedResidueMassSq_nonneg gamma xi)
        (Ne.symm hmass)
    simp [wooleyPolynomialNormalizedResidueGridSum, hmass,
      Real.sqrt_ne_zero'.mpr hmassPos]

theorem wooleyPolynomial_sum_weightedResidueGridSum
    {Q k qB qH : ℕ} (phi : WooleyPolynomialSystem k)
    [NeZero qB] [NeZero qH] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) :
    ∑ xi : ZMod qH,
        wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha xi =
      wooleyPolynomialWeightedGridSum phi qB gamma alpha := by
  unfold wooleyPolynomialWeightedResidueGridSum
    wooleyPolynomialWeightedGridSum wooleyResidueClass
  rw [Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Fin Q)))
    (g := fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)))
    (f := fun n : Fin Q =>
      gamma n * wooleyPolynomialGridPhase phi qB Q alpha n)]

theorem wooleyPolynomial_normalizedGridSum_decomposition
    {Q k qB qH : ℕ} (phi : WooleyPolynomialSystem k)
    [NeZero qB] [NeZero qH] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB)
    (hmass : wooleyWeightedMassSq gamma ≠ 0) :
    wooleyPolynomialNormalizedGridSum phi qB gamma alpha =
      ((Real.sqrt (wooleyWeightedMassSq gamma) : ℂ)⁻¹) *
        ∑ xi : ZMod qH,
          (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
            wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi := by
  simp_rw [wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    phi gamma alpha]
  rw [wooleyPolynomial_sum_weightedResidueGridSum phi gamma alpha]
  simp [wooleyPolynomialNormalizedGridSum, hmass]

/-- Polynomial-system equation (3.9), with the exact normalization. -/
theorem wooleyPolynomial_equation_3_9
    {Q k qB qH s : ℕ} (phi : WooleyPolynomialSystem k)
    [NeZero qB] [NeZero qH]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (hs : 1 ≤ s) (hmass : wooleyWeightedMassSq gamma ≠ 0) :
    ‖wooleyPolynomialNormalizedGridSum phi qB gamma alpha‖ ^ (2 * s) ≤
      (qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
        ∑ xi : ZMod qH,
          wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi‖ ^ (2 * s) := by
  let M := wooleyWeightedMassSq gamma
  let S : ℂ := ∑ xi : ZMod qH,
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
      wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha xi
  let R : ℝ := ∑ xi : ZMod qH,
    wooleyWeightedResidueMassSq gamma xi *
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi qB gamma alpha xi‖ ^ (2 * s)
  have hM : 0 < M := lt_of_le_of_ne
    (wooleyWeightedMassSq_nonneg gamma) (Ne.symm hmass)
  have hdecomp := wooleyPolynomial_normalizedGridSum_decomposition
    (qH := qH) phi gamma alpha hmass
  have hholder := wooley_weighted_complex_sum_pow_le
    (Finset.univ : Finset (ZMod qH))
    (fun xi => wooleyWeightedResidueMassSq gamma xi)
    (fun xi => wooleyPolynomialNormalizedResidueGridSum
      phi qB gamma alpha xi) hs
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
          ((qH : ℝ) ^ s * M ^ (s - 1) * R) := by gcongr
    _ = (qH : ℝ) ^ s * M⁻¹ * R := by
      calc
        (Real.sqrt M)⁻¹ ^ (2 * s) *
            ((qH : ℝ) ^ s * M ^ (s - 1) * R) =
            (qH : ℝ) ^ s *
              ((Real.sqrt M)⁻¹ ^ (2 * s) * M ^ (s - 1)) * R := by ring
        _ = (qH : ℝ) ^ s * M⁻¹ * R := by
          rw [wooley_sqrt_inverse_power_mul hM hs]
    _ = _ := by rfl

/-- Polynomial-system equation (3.10). -/
theorem wooleyPolynomial_equation_3_10
    {Q k qB qH s : ℕ} (phi : WooleyPolynomialSystem k)
    [NeZero qB] [NeZero qH]
    (gamma : Fin Q → ℂ) (hs : 1 ≤ s) :
    wooleyPolynomialWeightedGridMean phi s qB gamma ≤
      (qH : ℝ) ^ s *
        wooleyPolynomialConditionedGridMean phi s qB qH gamma := by
  by_cases hmass : wooleyWeightedMassSq gamma = 0
  · have hs0 : s ≠ 0 := by omega
    simp [wooleyPolynomialWeightedGridMean,
      wooleyPolynomialConditionedGridMean,
      wooleyPolynomialNormalizedGridSum, hmass, hs0]
  · have hpoint (alpha : Fin k → ZMod qB) :=
      wooleyPolynomial_equation_3_9 (qH := qH) phi gamma alpha hs hmass
    unfold wooleyPolynomialWeightedGridMean
      wooleyPolynomialConditionedGridMean
    rw [if_neg hmass]
    have hscale : (0 : ℝ) ≤ (((qB ^ k : ℕ) : ℝ))⁻¹ := by positivity
    calc
      (((qB ^ k : ℕ) : ℝ))⁻¹ *
          ∑ alpha : Fin k → ZMod qB,
            ‖wooleyPolynomialNormalizedGridSum
              phi qB gamma alpha‖ ^ (2 * s) ≤
        (((qB ^ k : ℕ) : ℝ))⁻¹ *
          ∑ alpha : Fin k → ZMod qB,
            ((qH : ℝ) ^ s * (wooleyWeightedMassSq gamma)⁻¹ *
              ∑ xi : ZMod qH,
                wooleyWeightedResidueMassSq gamma xi *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi qB gamma alpha xi‖ ^ (2 * s)) := by
          apply mul_le_mul_of_nonneg_left _ hscale
          exact Finset.sum_le_sum fun alpha _ => hpoint alpha
      _ = (qH : ℝ) ^ s *
          ((wooleyWeightedMassSq gamma)⁻¹ *
            ∑ xi : ZMod qH,
              wooleyWeightedResidueMassSq gamma xi *
                ((((qB ^ k : ℕ) : ℝ))⁻¹ *
                  ∑ alpha : Fin k → ZMod qB,
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi qB gamma alpha xi‖ ^ (2 * s))) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro xi hxi
        apply Finset.sum_congr rfl
        intro alpha halpha
        ac_rfl

#print axioms wooleyPolynomialResidueGridSum_eq_zero_of_massSq_eq_zero
#print axioms wooleyPolynomial_normalizedGridSum_decomposition
#print axioms wooleyPolynomial_equation_3_9
#print axioms wooleyPolynomial_equation_3_10

end

end GafniTao
