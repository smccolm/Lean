import GafniTao.WooleySourceBoxing

/-!
# Source mixed means for nested efficient congruencing

Wooley's Corollary 3.2 is stated for finitely supported sequences on all of
`ℤ`, whereas the initial finite development of (3.19)--(3.20) used a box
`Fin Q`.  This file defines the literal source versions of the local and
aggregate mixed means and proves that the box embedding preserves them
exactly.  Thus every later passage between source sequences and finite boxes
has a checked normalization bridge.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The source-sequence version of the local mixed mean (3.20). -/
def wooleySourcePolynomialMixedResidueMoment {k : ℕ}
    (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) : ℝ :=
  (((p ^ B) ^ k : ℕ) : ℝ)⁻¹ *
    ∑ alpha : Fin k → ZMod (p ^ B),
      ‖wooleySourceNormalizedPolynomialResidueSum
          phi gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
        ‖wooleySourceNormalizedPolynomialResidueSum
          phi gamma alpha eta‖ ^
            (2 * (s - wooleyTriangular r))

/-- The literal source-sequence version of `K^r_{a,b}` from (3.19). -/
def wooleySourcePolynomialMixedMean {k : ℕ}
    (phi : WooleyPolynomialSystem k)
    (s r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) : ℝ :=
  if wooleySourceMassSq gamma = 0 then 0
  else (wooleySourceMassSq gamma)⁻¹ ^ 2 *
    ∑ xi : ZMod (p ^ a),
      ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
        wooleySourceResidueMassSq gamma (p ^ a) xi *
          wooleySourceResidueMassSq gamma (p ^ b) eta *
            wooleySourcePolynomialMixedResidueMoment
              phi s r p B a b gamma xi eta

theorem wooleySourcePolynomialMixedResidueMoment_nonneg
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) :
    0 ≤ wooleySourcePolynomialMixedResidueMoment
      phi s r p B a b gamma xi eta := by
  unfold wooleySourcePolynomialMixedResidueMoment
  positivity

theorem wooleySourcePolynomialMixedMean_nonneg
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) :
    0 ≤ wooleySourcePolynomialMixedMean
      phi s r p B a b nu gamma := by
  unfold wooleySourcePolynomialMixedMean
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro xi hxi
    apply Finset.sum_nonneg
    intro eta heta
    exact mul_nonneg
      (mul_nonneg
        (wooleySourceResidueMassSq_nonneg gamma (p ^ a) xi)
        (wooleySourceResidueMassSq_nonneg gamma (p ^ b) eta))
      (wooleySourcePolynomialMixedResidueMoment_nonneg
        phi s r p B a b gamma xi eta)

/-- The local source mixed moment of a box sequence is definitionally the
finite-box polynomial mixed moment, after the proved residue-sum bridge. -/
theorem wooleySourcePolynomialMixedResidueMoment_box
    {Q k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) :
    wooleySourcePolynomialMixedResidueMoment phi s r p B a b
        (wooleyBoxSourceSequence gamma) xi eta =
      wooleyPolynomialMixedResidueGridMoment
        phi s r p B a b gamma xi eta := by
  unfold wooleySourcePolynomialMixedResidueMoment
    wooleyPolynomialMixedResidueGridMoment
  simp_rw [wooleySourceNormalizedPolynomialResidueSum_box]

/-- Exact source/finite-box bridge for (3.19). -/
theorem wooleySourcePolynomialMixedMean_box
    {Q k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu
        (wooleyBoxSourceSequence gamma) =
      wooleyPolynomialMixedGridMean phi s r p B a b nu gamma := by
  unfold wooleySourcePolynomialMixedMean wooleyPolynomialMixedGridMean
  rw [wooleyBoxSourceSequence_massSq]
  split_ifs
  · rfl
  · simp_rw [wooleySourceResidueMassSq_box,
      wooleySourcePolynomialMixedResidueMoment_box]

/-- Separation is inequality after reduction to the common depth.  The
depth hypotheses are exactly the divisibility assumptions used in (3.19). -/
theorem wooleyResiduesSeparated_iff_cast_ne
    {p a b nu : ℕ} [NeZero p] (hna : nu ≤ a) (hnb : nu ≤ b)
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :
    wooleyResiduesSeparated nu xi eta ↔
      ZMod.castHom (pow_dvd_pow p hna) (ZMod (p ^ nu)) xi ≠
        ZMod.castHom (pow_dvd_pow p hnb) (ZMod (p ^ nu)) eta := by
  unfold wooleyResiduesSeparated
  constructor
  · intro hval heq
    apply hval
    have h := congrArg ZMod.val heq
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.val_natCast] using h
  · intro hne hval
    apply hne
    apply ZMod.val_injective
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.val_natCast] using hval

/-- Adding the same integer to residue labels at two depths preserves the
source separation relation. -/
theorem wooleyResiduesSeparated_add_iff
    {p a b nu : ℕ} [NeZero p] (hna : nu ≤ a) (hnb : nu ≤ b)
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) (t : ℤ) :
    wooleyResiduesSeparated nu (xi + (t : ZMod (p ^ a)))
        (eta + (t : ZMod (p ^ b))) ↔
      wooleyResiduesSeparated nu xi eta := by
  rw [wooleyResiduesSeparated_iff_cast_ne hna hnb,
    wooleyResiduesSeparated_iff_cast_ne hna hnb]
  simp only [map_add, map_intCast]
  constructor
  · intro h hEq
    apply h
    rw [hEq]
  · intro h hEq
    apply h
    exact add_right_cancel hEq

/-- A simultaneous translation of coefficients and polynomial arguments
only translates the two residue labels in the local mixed moment. -/
theorem wooleySourcePolynomialMixedResidueMoment_affinePullback_one
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) (t : ℤ) :
    wooleySourcePolynomialMixedResidueMoment
        (wooleyAffinePolynomialSystem phi 1 t) s r p B a b
        (wooleyAffinePullback gamma 1 (by norm_num) t) xi eta =
      wooleySourcePolynomialMixedResidueMoment phi s r p B a b gamma
        (xi + (t : ZMod (p ^ a)))
        (eta + (t : ZMod (p ^ b))) := by
  unfold wooleySourcePolynomialMixedResidueMoment
  simp_rw [wooleySourceNormalizedPolynomialResidueSum_affinePullback_one]

/-- The aggregate source mixed mean is translation invariant whenever the
common separation depth is no larger than either residue depth. -/
theorem wooleySourcePolynomialMixedMean_affinePullback_one
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hna : nu ≤ a) (hnb : nu ≤ b)
    (gamma : WooleySourceSequence) (t : ℤ) :
    wooleySourcePolynomialMixedMean
        (wooleyAffinePolynomialSystem phi 1 t) s r p B a b nu
        (wooleyAffinePullback gamma 1 (by norm_num) t) =
      wooleySourcePolynomialMixedMean phi s r p B a b nu gamma := by
  unfold wooleySourcePolynomialMixedMean
  rw [wooleySourceMassSq_affinePullback_one]
  split_ifs
  · rfl
  · simp_rw [wooleySourceResidueMassSq_affinePullback_one,
      wooleySourcePolynomialMixedResidueMoment_affinePullback_one]
    let eA : ZMod (p ^ a) ≃ ZMod (p ^ a) :=
      Equiv.addRight (t : ZMod (p ^ a))
    let eB : ZMod (p ^ b) ≃ ZMod (p ^ b) :=
      Equiv.addRight (t : ZMod (p ^ b))
    let F : ZMod (p ^ a) → ZMod (p ^ b) → ℝ := fun xi eta =>
      wooleySourceResidueMassSq gamma (p ^ a) xi *
        wooleySourceResidueMassSq gamma (p ^ b) eta *
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B a b gamma xi eta
    have hinner (xi : ZMod (p ^ a)) :
        (∑ eta : ZMod (p ^ b),
          if wooleyResiduesSeparated nu xi eta then
            F (eA xi) (eB eta) else 0) =
        ∑ eta : ZMod (p ^ b),
          if wooleyResiduesSeparated nu (eA xi) eta then
            F (eA xi) eta else 0 := by
      have hsum := eB.sum_comp (fun eta : ZMod (p ^ b) =>
        if wooleyResiduesSeparated nu (eA xi) eta then
          F (eA xi) eta else 0)
      have hsep (eta : ZMod (p ^ b)) :
          wooleyResiduesSeparated nu (eA xi) (eB eta) ↔
            wooleyResiduesSeparated nu xi eta := by
        exact wooleyResiduesSeparated_add_iff hna hnb xi eta t
      simpa only [eA, eB, hsep] using hsum
    have houter := eA.sum_comp (fun xi : ZMod (p ^ a) =>
      ∑ eta : ZMod (p ^ b),
        if wooleyResiduesSeparated nu xi eta then F xi eta else 0)
    simp_rw [Finset.sum_filter]
    apply congrArg (fun x : ℝ => (wooleySourceMassSq gamma)⁻¹ ^ 2 * x)
    calc
      (∑ xi : ZMod (p ^ a),
          ∑ eta : ZMod (p ^ b),
            if wooleyResiduesSeparated nu xi eta then
              F (eA xi) (eB eta) else 0) =
          ∑ xi : ZMod (p ^ a),
            ∑ eta : ZMod (p ^ b),
              if wooleyResiduesSeparated nu (eA xi) eta then
                F (eA xi) eta else 0 :=
        Finset.sum_congr rfl fun xi _ => hinner xi
      _ = ∑ xi : ZMod (p ^ a),
          ∑ eta : ZMod (p ^ b),
            if wooleyResiduesSeparated nu xi eta then F xi eta else 0 :=
        houter

/-- Every literal source mixed mean is exactly a finite-box polynomial mixed
mean after the same checked translation used for the global and conditioned
means. -/
theorem wooleySourcePolynomialMixedMean_eq_boxed
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hna : nu ≤ a) (hnb : nu ≤ b)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma =
      wooleyPolynomialMixedGridMean
        (wooleyBoxedPolynomialSystem phi gamma) s r p B a b nu
        (wooleySourceBoxCoefficients gamma) := by
  calc
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma =
        wooleySourcePolynomialMixedMean
          (wooleyBoxedPolynomialSystem phi gamma) s r p B a b nu
          (wooleyBoxedSourceSequence gamma) :=
      (wooleySourcePolynomialMixedMean_affinePullback_one
        phi s r p B a b nu hna hnb gamma
          (-((wooleySourceRadius gamma + 1 : ℕ) : ℤ))).symm
    _ = wooleySourcePolynomialMixedMean
          (wooleyBoxedPolynomialSystem phi gamma) s r p B a b nu
          (wooleyBoxSourceSequence (wooleySourceBoxCoefficients gamma)) := by
      rw [wooleyBoxSourceSequence_boxCoefficients]
    _ = _ := wooleySourcePolynomialMixedMean_box _ _ _ _ _ _ _ _ _

#print axioms wooleySourcePolynomialMixedResidueMoment_nonneg
#print axioms wooleySourcePolynomialMixedMean_nonneg
#print axioms wooleySourcePolynomialMixedResidueMoment_box
#print axioms wooleySourcePolynomialMixedMean_box
#print axioms wooleyResiduesSeparated_iff_cast_ne
#print axioms wooleyResiduesSeparated_add_iff
#print axioms wooleySourcePolynomialMixedResidueMoment_affinePullback_one
#print axioms wooleySourcePolynomialMixedMean_affinePullback_one
#print axioms wooleySourcePolynomialMixedMean_eq_boxed

end

end GafniTao
