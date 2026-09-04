import GafniTao.WooleySourceRestriction

/-!
# Affine reindexing of Wooley source sequences

This is the exact finite-support implementation of (4.2)--(4.3): after
restricting to `n ≡ xi (mod q)`, write `n = q*y + xi`.  The map is an
embedding when `q > 0`, and its image is exactly that residue class.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The arithmetic-progression embedding `y ↦ q*y+xi`. -/
def wooleyAffineEmbedding (q : ℕ) (hq : 0 < q) (xi : ℤ) : ℤ ↪ ℤ where
  toFun y := (q : ℤ) * y + xi
  inj' := by
    intro y z h
    have hmul : (q : ℤ) * y = (q : ℤ) * z := by linarith
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne') hmul

@[simp] theorem wooleyAffineEmbedding_apply
    (q : ℕ) (hq : 0 < q) (xi y : ℤ) :
    wooleyAffineEmbedding q hq xi y = (q : ℤ) * y + xi :=
  rfl

/-- The image of the progression embedding is exactly one residue class. -/
theorem mem_range_wooleyAffineEmbedding_iff
    (q : ℕ) (hq : 0 < q) (xi n : ℤ) :
    n ∈ Set.range (wooleyAffineEmbedding q hq xi) ↔
      (n : ZMod q) = (xi : ZMod q) := by
  constructor
  · rintro ⟨y, rfl⟩
    simp [wooleyAffineEmbedding]
  · intro hn
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hn
    obtain ⟨d, hd⟩ := hn
    refine ⟨-d, ?_⟩
    change (q : ℤ) * (-d) + xi = n
    linarith

/-- Pull the original coefficients back along the selected progression. -/
def wooleyAffinePullback (gamma : WooleySourceSequence)
    (q : ℕ) (hq : 0 < q) (xi : ℤ) : WooleySourceSequence :=
  Finsupp.comapDomain (wooleyAffineEmbedding q hq xi) gamma
    (wooleyAffineEmbedding q hq xi).injective.injOn

@[simp] theorem wooleyAffinePullback_apply
    (gamma : WooleySourceSequence) (q : ℕ) (hq : 0 < q)
    (xi y : ℤ) :
    wooleyAffinePullback gamma q hq xi y = gamma ((q : ℤ) * y + xi) :=
  rfl

theorem WooleySourceSequence.Admissible.affinePullback
    {gamma : WooleySourceSequence} (hgamma : gamma.Admissible)
    (q : ℕ) (hq : 0 < q) (xi : ℤ) :
    (wooleyAffinePullback gamma q hq xi).Admissible := by
  intro y
  rw [wooleyAffinePullback_apply]
  exact hgamma _

/-- The support of the pullback maps bijectively to the part of the source
support in the selected residue class. -/
theorem wooleyAffineEmbedding_bijOn_support
    (gamma : WooleySourceSequence) (q : ℕ) (hq : 0 < q) (xi : ℤ) :
    Set.BijOn (wooleyAffineEmbedding q hq xi)
      ((wooleyAffineEmbedding q hq xi) ⁻¹'
        (↑(gamma.support.filter fun n : ℤ =>
          (n : ZMod q) = (xi : ZMod q)) : Set ℤ))
      (↑(gamma.support.filter fun n : ℤ =>
        (n : ZMod q) = (xi : ZMod q)) : Set ℤ) := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro y hy
    exact hy
  · exact (wooleyAffineEmbedding q hq xi).injective.injOn
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter] at hn
    obtain ⟨y, hy⟩ :=
      (mem_range_wooleyAffineEmbedding_iff q hq xi n).mpr hn.2
    refine ⟨y, ?_, hy⟩
    change wooleyAffineEmbedding q hq xi y ∈
      gamma.support.filter fun m : ℤ => (m : ZMod q) = (xi : ZMod q)
    simpa only [hy, Finset.mem_filter] using hn

/-- Equation (4.3) preserves the `L²` mass exactly. -/
theorem wooleySourceMassSq_affinePullback
    (gamma : WooleySourceSequence) (q : ℕ) (hq : 0 < q) (xi : ℤ) :
    wooleySourceMassSq (wooleyAffinePullback gamma q hq xi) =
      wooleySourceResidueMassSq gamma q (xi : ZMod q) := by
  unfold wooleySourceMassSq wooleySourceResidueMassSq wooleyAffinePullback
  rw [Finsupp.comapDomain_support]
  have hsupp :
      gamma.support.preimage (wooleyAffineEmbedding q hq xi)
          (wooleyAffineEmbedding q hq xi).injective.injOn =
        (gamma.support.filter fun n : ℤ =>
          (n : ZMod q) = (xi : ZMod q)).preimage
            (wooleyAffineEmbedding q hq xi)
            (wooleyAffineEmbedding q hq xi).injective.injOn := by
    ext y
    simp only [Finset.mem_preimage, Finset.mem_filter]
    constructor
    · intro hy
      exact ⟨hy,
        (mem_range_wooleyAffineEmbedding_iff q hq xi _).mp ⟨y, rfl⟩⟩
    · exact fun hy => hy.1
  rw [hsupp]
  exact Finset.sum_preimage_of_bij
    (wooleyAffineEmbedding q hq xi)
    (gamma.support.filter fun n : ℤ => (n : ZMod q) = (xi : ZMod q))
    (wooleyAffineEmbedding_bijOn_support gamma q hq xi)
    (fun n => ‖gamma n‖ ^ 2)

/-- Substitute `t = q*y+xi` in every polynomial.  Constants are retained;
this is the literal system occurring in (4.2)--(4.5), before the invertible
triangular normalization used to obtain (4.8). -/
def wooleyAffinePolynomialSystem {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ) (xi : ℤ) :
    WooleyPolynomialSystem k :=
  fun j => (phi j).comp (Polynomial.C (q : ℤ) * Polynomial.X +
    Polynomial.C xi)

theorem wooleyAffinePolynomialSystem_eval {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ) (xi y : ℤ) (j : Fin k) :
    (wooleyAffinePolynomialSystem phi q xi j).eval y =
      (phi j).eval ((q : ℤ) * y + xi) := by
  simp [wooleyAffinePolynomialSystem]

theorem wooleySourcePolynomialPhase_affine
    {k qB q : ℕ} [NeZero qB]
    (phi : WooleyPolynomialSystem k) (alpha : Fin k → ZMod qB)
    (xi y : ℤ) :
    wooleySourcePolynomialPhase (wooleyAffinePolynomialSystem phi q xi)
        alpha y =
      wooleySourcePolynomialPhase phi alpha ((q : ℤ) * y + xi) := by
  unfold wooleySourcePolynomialPhase
  simp_rw [wooleyAffinePolynomialSystem_eval]

/-- Exact sum-level form of (4.2)--(4.3). -/
theorem wooleySourcePolynomialSum_affinePullback
    {k qB q : ℕ} [NeZero qB] (hq : 0 < q)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod qB) (xi : ℤ) :
    wooleySourcePolynomialSum (wooleyAffinePolynomialSystem phi q xi)
        (wooleyAffinePullback gamma q hq xi) alpha =
      wooleySourcePolynomialResidueSum phi gamma alpha (xi : ZMod q) := by
  unfold wooleySourcePolynomialSum wooleySourcePolynomialResidueSum
    wooleyAffinePullback
  rw [Finsupp.comapDomain_support]
  have hsupp :
      gamma.support.preimage (wooleyAffineEmbedding q hq xi)
          (wooleyAffineEmbedding q hq xi).injective.injOn =
        (gamma.support.filter fun n : ℤ =>
          (n : ZMod q) = (xi : ZMod q)).preimage
            (wooleyAffineEmbedding q hq xi)
            (wooleyAffineEmbedding q hq xi).injective.injOn := by
    ext y
    simp only [Finset.mem_preimage, Finset.mem_filter]
    constructor
    · intro hy
      exact ⟨hy,
        (mem_range_wooleyAffineEmbedding_iff q hq xi _).mp ⟨y, rfl⟩⟩
    · exact fun hy => hy.1
  rw [hsupp]
  simpa only [Finsupp.comapDomain_apply, wooleyAffineEmbedding_apply,
    wooleySourcePolynomialPhase_affine] using
      Finset.sum_preimage_of_bij
        (wooleyAffineEmbedding q hq xi)
        (gamma.support.filter fun n : ℤ =>
          (n : ZMod q) = (xi : ZMod q))
        (wooleyAffineEmbedding_bijOn_support gamma q hq xi)
        (fun n => gamma n * wooleySourcePolynomialPhase phi alpha n)

/-- Exact normalized form of the progression reindexing. -/
theorem wooleySourceNormalizedPolynomialSum_affinePullback
    {k qB q : ℕ} [NeZero qB] (hq : 0 < q)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod qB) (xi : ℤ) :
    wooleySourceNormalizedPolynomialSum
        (wooleyAffinePolynomialSystem phi q xi)
        (wooleyAffinePullback gamma q hq xi) alpha =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        (xi : ZMod q) := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleySourceNormalizedPolynomialResidueSum
  rw [wooleySourceMassSq_affinePullback,
    wooleySourcePolynomialSum_affinePullback]

/-- Restriction commutes with an integral translation, with the residue
label translated by the same amount. -/
theorem wooleySourceResidueSequence_affinePullback_one
    (gamma : WooleySourceSequence) (q : ℕ) (z : ZMod q) (t : ℤ) :
    wooleySourceResidueSequence
        (wooleyAffinePullback gamma 1 (by norm_num) t) q z =
      wooleyAffinePullback
        (wooleySourceResidueSequence gamma q (z + (t : ZMod q)))
        1 (by norm_num) t := by
  ext y
  simp only [wooleySourceResidueSequence_apply,
    wooleyAffinePullback_apply]
  norm_num

/-- Residue masses are permuted, not changed, by translation. -/
theorem wooleySourceResidueMassSq_affinePullback_one
    (gamma : WooleySourceSequence) (q : ℕ) (z : ZMod q) (t : ℤ) :
    wooleySourceResidueMassSq
        (wooleyAffinePullback gamma 1 (by norm_num) t) q z =
      wooleySourceResidueMassSq gamma q (z + (t : ZMod q)) := by
  rw [← wooleySourceMassSq_residueSequence,
    wooleySourceResidueSequence_affinePullback_one,
    wooleySourceMassSq_affinePullback,
    wooleySourceResidueMassSq_mod_one,
    wooleySourceMassSq_residueSequence]

/-- The normalized residue sum is likewise permuted by a simultaneous
translation of coefficients and polynomials. -/
theorem wooleySourceNormalizedPolynomialResidueSum_affinePullback_one
    {k qB q : ℕ} [NeZero qB]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod qB) (z : ZMod q) (t : ℤ) :
    wooleySourceNormalizedPolynomialResidueSum
        (wooleyAffinePolynomialSystem phi 1 t)
        (wooleyAffinePullback gamma 1 (by norm_num) t) alpha z =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        (z + (t : ZMod q)) := by
  rw [← wooleySourceNormalizedPolynomialSum_residueSequence]
  rw [wooleySourceResidueSequence_affinePullback_one]
  rw [wooleySourceNormalizedPolynomialSum_affinePullback]
  rw [wooleySourceNormalizedPolynomialResidueSum_mod_one]
  rw [wooleySourceNormalizedPolynomialSum_residueSequence]

/-- Translation preserves total coefficient mass. -/
theorem wooleySourceMassSq_affinePullback_one
    (gamma : WooleySourceSequence) (t : ℤ) :
    wooleySourceMassSq (wooleyAffinePullback gamma 1 (by norm_num) t) =
      wooleySourceMassSq gamma := by
  rw [wooleySourceMassSq_affinePullback,
    wooleySourceResidueMassSq_mod_one]

/-- Simultaneously translating the coefficients and polynomial arguments
preserves the conditioned mean; it merely permutes its residue classes. -/
theorem wooleySourcePolynomialConditionedMean_affinePullback_one
    {k qB qH s : ℕ} [NeZero qB] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (t : ℤ) :
    wooleySourcePolynomialConditionedMean s qB qH
        (wooleyAffinePolynomialSystem phi 1 t)
        (wooleyAffinePullback gamma 1 (by norm_num) t) =
      wooleySourcePolynomialConditionedMean s qB qH phi gamma := by
  unfold wooleySourcePolynomialConditionedMean
  rw [wooleySourceMassSq_affinePullback_one]
  split_ifs
  · rfl
  · simp_rw [wooleySourceResidueMassSq_affinePullback_one,
      wooleySourceNormalizedPolynomialResidueSum_affinePullback_one]
    let e : ZMod qH ≃ ZMod qH := Equiv.addRight (t : ZMod qH)
    have hsum := e.sum_comp (fun z : ZMod qH =>
      wooleySourceResidueMassSq gamma qH z *
        ((((qB ^ k : ℕ) : ℝ))⁻¹ *
          ∑ alpha : Fin k → ZMod qB,
            ‖wooleySourceNormalizedPolynomialResidueSum
              phi gamma alpha z‖ ^ (2 * s)))
    exact congrArg (fun x : ℝ => (wooleySourceMassSq gamma)⁻¹ * x) hsum

#print axioms wooleyAffineEmbedding_apply
#print axioms mem_range_wooleyAffineEmbedding_iff
#print axioms wooleyAffinePullback_apply
#print axioms WooleySourceSequence.Admissible.affinePullback
#print axioms wooleyAffineEmbedding_bijOn_support
#print axioms wooleySourceMassSq_affinePullback
#print axioms wooleyAffinePolynomialSystem_eval
#print axioms wooleySourcePolynomialPhase_affine
#print axioms wooleySourcePolynomialSum_affinePullback
#print axioms wooleySourceNormalizedPolynomialSum_affinePullback
#print axioms wooleySourceResidueSequence_affinePullback_one
#print axioms wooleySourceResidueMassSq_affinePullback_one
#print axioms wooleySourceNormalizedPolynomialResidueSum_affinePullback_one
#print axioms wooleySourceMassSq_affinePullback_one
#print axioms wooleySourcePolynomialConditionedMean_affinePullback_one

end

end GafniTao
