import GafniTao.WooleyMixedRadix
import GafniTao.WooleyAffineComposition

/-!
# The conditioning tower in Wooley equation (4.14)

This file proves that conditioning first modulo `q₁` and then modulo `q₂`
is exactly conditioning once modulo `q₁*q₂`.  The weights are the actual
source `L²` residue masses, and the polynomial system and coefficient
sequence are transported by the literal affine pullback.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The inner residue-class mean occurring in the definition of
`U^{B,h}_{s,k}`. -/
def wooleySourcePolynomialResidueMean {k : ℕ}
    (s q qH : ℕ) [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (xi : ZMod qH) : ℝ :=
  ((q ^ k : ℕ) : ℝ)⁻¹ *
    ∑ alpha : Fin k → ZMod q,
      ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi‖ ^
        (2 * s)

/-- Multiplying a conditioned mean by its total mass exposes its exact
weighted residue expansion, including the zero-mass branch. -/
theorem wooleySourceMassSq_mul_conditionedMean
    {k s q qH : ℕ} [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean s q qH phi gamma =
      ∑ xi : ZMod qH,
        wooleySourceResidueMassSq gamma qH xi *
          wooleySourcePolynomialResidueMean s q qH phi gamma xi := by
  unfold wooleySourcePolynomialConditionedMean
    wooleySourcePolynomialResidueMean
  by_cases hmass : wooleySourceMassSq gamma = 0
  · rw [if_pos hmass, hmass, zero_mul]
    have hsum : ∑ xi : ZMod qH,
        wooleySourceResidueMassSq gamma qH xi = 0 := by
      rw [wooleySource_sum_residueMassSq, hmass]
    have hzero : ∀ xi : ZMod qH,
        wooleySourceResidueMassSq gamma qH xi = 0 := by
      intro xi
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun z hz => wooleySourceResidueMassSq_nonneg gamma qH z)).mp
          hsum xi (Finset.mem_univ xi)
    simp_rw [hzero]
    simp
  · rw [if_neg hmass, ← mul_assoc, mul_inv_cancel₀ hmass, one_mul]

/-- Equation (4.2) after Fourier averaging: a residue-class mean is the
ordinary mean of the affine pullback sequence and affine polynomial system. -/
theorem wooleySourcePolynomialMean_affinePullback
    {k s q q₁ : ℕ} [NeZero q] [NeZero q₁]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (xi : ZMod q₁) :
    wooleySourcePolynomialMean s q
        (wooleyAffinePolynomialSystem phi q₁ xi.val)
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) =
      wooleySourcePolynomialResidueMean s q q₁ phi gamma xi := by
  unfold wooleySourcePolynomialMean wooleySourcePolynomialResidueMean
  apply congrArg (fun x : ℝ => ((q ^ k : ℕ) : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro alpha halpha
  rw [wooleySourceNormalizedPolynomialSum_affinePullback]
  have hxi : (((xi.val : ℕ) : ℤ) : ZMod q₁) = xi := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val xi
  rw [hxi]

/-- Exact equation (4.2) summed over the initial residue classes. -/
theorem wooleySourceMassSq_mul_conditionedMean_eq_affineSum
    {k s q q₁ : ℕ} [NeZero q] [NeZero q₁]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean s q q₁ phi gamma =
      ∑ xi : ZMod q₁,
        wooleySourceResidueMassSq gamma q₁ xi *
          wooleySourcePolynomialMean s q
            (wooleyAffinePolynomialSystem phi q₁ xi.val)
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) := by
  rw [wooleySourceMassSq_mul_conditionedMean]
  apply Finset.sum_congr rfl
  intro xi hxi
  rw [wooleySourcePolynomialMean_affinePullback]

/-- The local residue mass after an affine pullback is the mass of the
corresponding mixed-radix residue in the original sequence. -/
theorem wooleySourceResidueMassSq_affinePullback_mixedRadix
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (gamma : WooleySourceSequence) (xi : ZMod q₁) (eta : ZMod q₂) :
    wooleySourceResidueMassSq
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
        q₂ eta =
      wooleySourceResidueMassSq gamma (q₂ * q₁)
        (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) := by
  have heta : (((eta.val : ℕ) : ℤ) : ZMod q₂) = eta := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val eta
  calc
    wooleySourceResidueMassSq
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
        q₂ eta =
      wooleySourceResidueMassSq
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
        q₂ (((eta.val : ℕ) : ℤ) : ZMod q₂) := by rw [heta]
    _ = wooleySourceResidueMassSq gamma (q₁ * q₂)
        ((((q₁ : ℤ) * eta.val + xi.val : ℤ)) : ZMod (q₁ * q₂)) :=
      wooleySourceResidueMassSq_affinePullback gamma q₁ q₂
        (NeZero.pos q₁) (NeZero.pos q₂) xi.val eta.val
    _ = wooleySourceResidueMassSq gamma (q₂ * q₁)
        (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) := by
      rw [Nat.mul_comm q₁ q₂]
      congr 1
      rw [wooleyMixedRadixEquiv_apply]
      push_cast
      ring

/-- The local normalized residue mean is likewise transported exactly. -/
theorem wooleySourcePolynomialResidueMean_affinePullback_mixedRadix
    {k s q q₁ q₂ : ℕ} [NeZero q] [NeZero q₁] [NeZero q₂]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (xi : ZMod q₁) (eta : ZMod q₂) :
    wooleySourcePolynomialResidueMean s q q₂
        (wooleyAffinePolynomialSystem phi q₁ xi.val)
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) eta =
      wooleySourcePolynomialResidueMean s q (q₂ * q₁) phi gamma
        (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) := by
  unfold wooleySourcePolynomialResidueMean
  apply congrArg (fun x : ℝ => ((q ^ k : ℕ) : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro alpha halpha
  congr 1
  apply congrArg norm
  have heta : (((eta.val : ℕ) : ℤ) : ZMod q₂) = eta := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val eta
  calc
    wooleySourceNormalizedPolynomialResidueSum
        (wooleyAffinePolynomialSystem phi q₁ xi.val)
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
        alpha eta =
      wooleySourceNormalizedPolynomialResidueSum
        (wooleyAffinePolynomialSystem phi q₁ xi.val)
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
        alpha (((eta.val : ℕ) : ℤ) : ZMod q₂) := by rw [heta]
    _ = wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        ((((q₁ : ℤ) * eta.val + xi.val : ℤ)) : ZMod (q₁ * q₂)) :=
      wooleySourceNormalizedPolynomialResidueSum_affinePullback
        phi gamma alpha q₁ q₂ (NeZero.pos q₁) (NeZero.pos q₂)
          xi.val eta.val
    _ = wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) := by
      rw [Nat.mul_comm q₁ q₂]
      congr 1
      rw [wooleyMixedRadixEquiv_apply]
      push_cast
      ring

/-- Exact conditioning tower: the double sum over `(xi,eta)` in (4.14)
is the single sum over `zeta` modulo the product modulus. -/
theorem wooleySourcePolynomialConditionedMean_tower
    {k s q q₁ q₂ : ℕ} [NeZero q] [NeZero q₁] [NeZero q₂]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    ∑ xi : ZMod q₁,
        wooleySourceResidueMassSq gamma q₁ xi *
          wooleySourcePolynomialConditionedMean s q q₂
            (wooleyAffinePolynomialSystem phi q₁ xi.val)
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) =
      wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean s q (q₂ * q₁) phi gamma := by
  calc
    ∑ xi : ZMod q₁,
        wooleySourceResidueMassSq gamma q₁ xi *
          wooleySourcePolynomialConditionedMean s q q₂
            (wooleyAffinePolynomialSystem phi q₁ xi.val)
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) =
      ∑ xi : ZMod q₁,
        wooleySourceMassSq
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) *
          wooleySourcePolynomialConditionedMean s q q₂
            (wooleyAffinePolynomialSystem phi q₁ xi.val)
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) := by
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [wooleySourceMassSq_affinePullback]
      have hxiCast : (((xi.val : ℕ) : ℤ) : ZMod q₁) = xi := by
        simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val xi
      rw [hxiCast]
    _ = ∑ xi : ZMod q₁, ∑ eta : ZMod q₂,
        wooleySourceResidueMassSq
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) q₂ eta *
          wooleySourcePolynomialResidueMean s q q₂
            (wooleyAffinePolynomialSystem phi q₁ xi.val)
            (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val) eta := by
      apply Finset.sum_congr rfl
      intro xi hxi
      exact wooleySourceMassSq_mul_conditionedMean
        (wooleyAffinePolynomialSystem phi q₁ xi.val)
        (wooleyAffinePullback gamma q₁ (NeZero.pos q₁) xi.val)
    _ = ∑ xi : ZMod q₁, ∑ eta : ZMod q₂,
        wooleySourceResidueMassSq gamma (q₂ * q₁)
            (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) *
          wooleySourcePolynomialResidueMean s q (q₂ * q₁) phi gamma
            (wooleyMixedRadixEquiv q₁ q₂ (xi, eta)) := by
      apply Finset.sum_congr rfl
      intro xi hxi
      apply Finset.sum_congr rfl
      intro eta heta
      rw [wooleySourceResidueMassSq_affinePullback_mixedRadix,
        wooleySourcePolynomialResidueMean_affinePullback_mixedRadix]
    _ = ∑ zeta : ZMod (q₂ * q₁),
        wooleySourceResidueMassSq gamma (q₂ * q₁) zeta *
          wooleySourcePolynomialResidueMean s q (q₂ * q₁) phi gamma zeta := by
      exact wooley_sum_mixedRadix (fun zeta : ZMod (q₂ * q₁) =>
        wooleySourceResidueMassSq gamma (q₂ * q₁) zeta *
          wooleySourcePolynomialResidueMean s q (q₂ * q₁) phi gamma zeta)
    _ = wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean s q (q₂ * q₁) phi gamma :=
      (wooleySourceMassSq_mul_conditionedMean phi gamma).symm

/-- Prime-power form of the conditioning tower, with the exact identity
`p^(H-h) * p^h = p^H`. -/
theorem wooleySourcePolynomialConditionedMean_power_tower
    {k s q p h H : ℕ} [NeZero q] [NeZero p] (hH : h ≤ H)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    ∑ xi : ZMod (p ^ h),
        wooleySourceResidueMassSq gamma (p ^ h) xi *
          wooleySourcePolynomialConditionedMean s q (p ^ (H - h))
            (wooleyAffinePolynomialSystem phi (p ^ h) xi.val)
            (wooleyAffinePullback gamma (p ^ h) (pow_pos (NeZero.pos p) h)
              xi.val) =
      wooleySourceMassSq gamma *
        wooleySourcePolynomialConditionedMean s q (p ^ H) phi gamma := by
  simpa only [Nat.pow_sub_mul_pow p hH] using
    (wooleySourcePolynomialConditionedMean_tower
      (q₁ := p ^ h) (q₂ := p ^ (H - h)) phi gamma)

#print axioms wooleySourceMassSq_mul_conditionedMean
#print axioms wooleySourcePolynomialMean_affinePullback
#print axioms wooleySourceMassSq_mul_conditionedMean_eq_affineSum
#print axioms wooleySourceResidueMassSq_affinePullback_mixedRadix
#print axioms wooleySourcePolynomialResidueMean_affinePullback_mixedRadix
#print axioms wooleySourcePolynomialConditionedMean_tower
#print axioms wooleySourcePolynomialConditionedMean_power_tower

end

end GafniTao
