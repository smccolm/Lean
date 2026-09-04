import GafniTao.WooleySourceMean

/-!
# Exact residue restrictions for Wooley's source sequences

Equations (3.2)--(3.4), and the translation step (4.2)--(4.5), repeatedly
replace a finitely supported coefficient sequence by its restriction to one
residue class.  This file performs that operation on the actual integer-indexed
source sequence and proves that the source residue masses and exponential sums
are exactly the ordinary masses and sums of the restricted sequence.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The coefficient sequence restricted to the residue class `xi mod q`. -/
def wooleySourceResidueSequence (gamma : WooleySourceSequence)
    (q : ℕ) (xi : ZMod q) : WooleySourceSequence :=
  gamma.filter fun n : ℤ => (n : ZMod q) = xi

@[simp] theorem wooleySourceResidueSequence_apply
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q) (n : ℤ) :
    wooleySourceResidueSequence gamma q xi n =
      if (n : ZMod q) = xi then gamma n else 0 :=
  rfl

theorem wooleySourceResidueSequence_support
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q) :
    (wooleySourceResidueSequence gamma q xi).support =
      gamma.support.filter fun n : ℤ => (n : ZMod q) = xi :=
  rfl

theorem WooleySourceSequence.Admissible.residueSequence
    {gamma : WooleySourceSequence} (hgamma : gamma.Admissible)
    (q : ℕ) (xi : ZMod q) :
    (wooleySourceResidueSequence gamma q xi).Admissible := by
  intro n
  rw [wooleySourceResidueSequence_apply]
  split_ifs
  · exact hgamma n
  · simp

/-- Equation (4.3) at the coefficient-mass level, before the harmless affine
reindexing of the selected progression. -/
theorem wooleySourceMassSq_residueSequence
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q) :
    wooleySourceMassSq (wooleySourceResidueSequence gamma q xi) =
      wooleySourceResidueMassSq gamma q xi := by
  unfold wooleySourceMassSq wooleySourceResidueMassSq
  rw [wooleySourceResidueSequence_support]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_filter] at hn
  rw [wooleySourceResidueSequence_apply, if_pos hn.2]

/-- The global polynomial sum of the restricted sequence is the source
residue-class polynomial sum, with no error or change of normalization. -/
theorem wooleySourcePolynomialSum_residueSequence
    {k q qH : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourcePolynomialSum phi
        (wooleySourceResidueSequence gamma qH xi) alpha =
      wooleySourcePolynomialResidueSum phi gamma alpha xi := by
  unfold wooleySourcePolynomialSum wooleySourcePolynomialResidueSum
  rw [wooleySourceResidueSequence_support]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_filter] at hn
  rw [wooleySourceResidueSequence_apply, if_pos hn.2]

/-- Consequently the normalized global sum of a residue restriction is
literally the normalized residue sum in (3.4). -/
theorem wooleySourceNormalizedPolynomialSum_residueSequence
    {k q qH : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourceNormalizedPolynomialSum phi
        (wooleySourceResidueSequence gamma qH xi) alpha =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleySourceNormalizedPolynomialResidueSum
  rw [wooleySourceMassSq_residueSequence,
    wooleySourcePolynomialSum_residueSequence]

/-- Restricting first modulo `q` and then by another predicate is exactly
intersection of the two support conditions.  This is the finite-support form
used when a class modulo `p^h` is refined modulo `p^H`. -/
theorem wooleySourceResidueSequence_filter
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q)
    (P : ℤ → Prop) [DecidablePred P] :
    (wooleySourceResidueSequence gamma q xi).filter P =
      gamma.filter (fun n : ℤ => (n : ZMod q) = xi ∧ P n) := by
  ext n
  simp only [Finsupp.filter_apply, wooleySourceResidueSequence_apply]
  by_cases hq : (n : ZMod q) = xi <;> by_cases hP : P n <;> simp [hq, hP]

/-- A residue-class sequence is zero precisely when its source residue mass
is zero.  This makes the zero branch in (3.4) explicit. -/
theorem wooleySourceResidueSequence_eq_zero_iff
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q) :
    wooleySourceResidueSequence gamma q xi = 0 ↔
      wooleySourceResidueMassSq gamma q xi = 0 := by
  rw [← wooleySourceMassSq_residueSequence]
  constructor
  · intro h
    rw [h]
    simp [wooleySourceMassSq]
  · intro h
    apply Finsupp.ext
    intro n
    by_contra hn
    have hmem : n ∈ (wooleySourceResidueSequence gamma q xi).support :=
      Finsupp.mem_support_iff.mpr hn
    have hterm : 0 < ‖wooleySourceResidueSequence gamma q xi n‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr hn)
    have hle : ‖wooleySourceResidueSequence gamma q xi n‖ ^ 2 ≤
        wooleySourceMassSq (wooleySourceResidueSequence gamma q xi) := by
      unfold wooleySourceMassSq
      exact Finset.single_le_sum
        (fun m _ => sq_nonneg ‖wooleySourceResidueSequence gamma q xi m‖)
        hmem
    rw [h] at hle
    linarith

/-- Modulo one there is a single residue class, so its mass is the global
mass. -/
theorem wooleySourceResidueMassSq_mod_one
    (gamma : WooleySourceSequence) (xi : ZMod 1) :
    wooleySourceResidueMassSq gamma 1 xi = wooleySourceMassSq gamma := by
  have hxi : xi = 0 := Subsingleton.elim _ _
  subst xi
  unfold wooleySourceResidueMassSq wooleySourceMassSq
  have hf : gamma.support.filter (fun n : ℤ => (n : ZMod 1) = 0) =
      gamma.support := by
    exact Finset.filter_eq_self.mpr fun n hn => Subsingleton.elim _ _
  rw [hf]

/-- Modulo one the residue sum is the global sum. -/
theorem wooleySourcePolynomialResidueSum_mod_one
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q)
    (xi : ZMod 1) :
    wooleySourcePolynomialResidueSum phi gamma alpha xi =
      wooleySourcePolynomialSum phi gamma alpha := by
  have hxi : xi = 0 := Subsingleton.elim _ _
  subst xi
  unfold wooleySourcePolynomialResidueSum wooleySourcePolynomialSum
  have hf : gamma.support.filter (fun n : ℤ => (n : ZMod 1) = 0) =
      gamma.support := by
    exact Finset.filter_eq_self.mpr fun n hn => Subsingleton.elim _ _
  rw [hf]

/-- Modulo one the normalized residue sum is the normalized global sum. -/
theorem wooleySourceNormalizedPolynomialResidueSum_mod_one
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q)
    (xi : ZMod 1) :
    wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi =
      wooleySourceNormalizedPolynomialSum phi gamma alpha := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleySourceNormalizedPolynomialSum
  rw [wooleySourceResidueMassSq_mod_one,
    wooleySourcePolynomialResidueSum_mod_one]

#print axioms wooleySourceResidueSequence_apply
#print axioms wooleySourceResidueSequence_support
#print axioms WooleySourceSequence.Admissible.residueSequence
#print axioms wooleySourceMassSq_residueSequence
#print axioms wooleySourcePolynomialSum_residueSequence
#print axioms wooleySourceNormalizedPolynomialSum_residueSequence
#print axioms wooleySourceResidueSequence_filter
#print axioms wooleySourceResidueSequence_eq_zero_iff
#print axioms wooleySourceResidueMassSq_mod_one
#print axioms wooleySourcePolynomialResidueSum_mod_one
#print axioms wooleySourceNormalizedPolynomialResidueSum_mod_one

end

end GafniTao
