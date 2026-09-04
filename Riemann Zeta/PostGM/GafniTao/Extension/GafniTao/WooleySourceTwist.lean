import GafniTao.WooleySourceAffine

/-!
# Unit twists of Wooley source coefficients

The coefficient sequence in Wooley (7.14)--(7.16) is obtained by multiplying
an affine pullback by an additive character.  This file isolates the exact
finite-support operation and proves that a unit-modulus twist preserves the
support and every `L²` mass.  These are equalities, not estimates.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Multiply a finitely supported source sequence by an arbitrary function.
The support certificate records that multiplication cannot create support. -/
def wooleySourceTwist (gamma : WooleySourceSequence) (phase : ℤ → ℂ) :
    WooleySourceSequence :=
  Finsupp.onFinset gamma.support (fun n => gamma n * phase n) (by
    intro n hn
    by_contra hmem
    have hzero : gamma n = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hmem
    simp [hzero] at hn)

@[simp] theorem wooleySourceTwist_apply
    (gamma : WooleySourceSequence) (phase : ℤ → ℂ) (n : ℤ) :
    wooleySourceTwist gamma phase n = gamma n * phase n := by
  simp [wooleySourceTwist]

/-- A nowhere-zero phase preserves the support literally. -/
theorem wooleySourceTwist_support
    (gamma : WooleySourceSequence) (phase : ℤ → ℂ)
    (hphase : ∀ n, phase n ≠ 0) :
    (wooleySourceTwist gamma phase).support = gamma.support := by
  ext n
  simp only [Finsupp.mem_support_iff, wooleySourceTwist_apply]
  exact mul_ne_zero_iff_right (hphase n)

/-- Unit-modulus twisting preserves total coefficient mass. -/
theorem wooleySourceMassSq_twist
    (gamma : WooleySourceSequence) (phase : ℤ → ℂ)
    (hphase : ∀ n, ‖phase n‖ = 1) :
    wooleySourceMassSq (wooleySourceTwist gamma phase) =
      wooleySourceMassSq gamma := by
  have hne : ∀ n, phase n ≠ 0 := fun n => norm_ne_zero_iff.mp (by
    rw [hphase n]
    norm_num)
  unfold wooleySourceMassSq
  rw [wooleySourceTwist_support gamma phase hne]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wooleySourceTwist_apply, norm_mul, hphase]
  ring

/-- Unit-modulus twisting preserves every residue-class coefficient mass. -/
theorem wooleySourceResidueMassSq_twist
    (gamma : WooleySourceSequence) (phase : ℤ → ℂ)
    (hphase : ∀ n, ‖phase n‖ = 1) (q : ℕ) (xi : ZMod q) :
    wooleySourceResidueMassSq (wooleySourceTwist gamma phase) q xi =
      wooleySourceResidueMassSq gamma q xi := by
  have hne : ∀ n, phase n ≠ 0 := fun n => norm_ne_zero_iff.mp (by
    rw [hphase n]
    norm_num)
  unfold wooleySourceResidueMassSq
  rw [wooleySourceTwist_support gamma phase hne]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wooleySourceTwist_apply, norm_mul, hphase]
  ring

theorem WooleySourceSequence.Admissible.twist
    {gamma : WooleySourceSequence} (hgamma : gamma.Admissible)
    (phase : ℤ → ℂ) (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    (wooleySourceTwist gamma phase).Admissible := by
  intro n
  rw [wooleySourceTwist_apply, norm_mul]
  calc
    ‖gamma n‖ * ‖phase n‖ ≤ ‖gamma n‖ * 1 :=
      mul_le_mul_of_nonneg_left (hphase n) (norm_nonneg _)
    _ ≤ 1 := by simpa using hgamma n

theorem wooleySourcePolynomialPhase_norm
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (alpha : Fin k → ZMod q) (n : ℤ) :
    ‖wooleySourcePolynomialPhase phi alpha n‖ = 1 := by
  simp [wooleySourcePolynomialPhase, ZMod.stdAddChar_apply]

theorem wooleySourcePolynomialPhase_ne_zero
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (alpha : Fin k → ZMod q) (n : ℤ) :
    wooleySourcePolynomialPhase phi alpha n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [wooleySourcePolynomialPhase_norm]
  norm_num

theorem wooleySourcePolynomialPhase_zero
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k) (n : ℤ) :
    wooleySourcePolynomialPhase phi (0 : Fin k → ZMod q) n = 1 := by
  simp [wooleySourcePolynomialPhase]

/-- A source sequence twisted by its polynomial phase has ordinary coefficient
sum equal to the corresponding unnormalised exponential sum. -/
theorem wooleySource_sum_twist_eq_polynomialSum
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q) :
    ∑ n ∈ (wooleySourceTwist gamma
          (fun y => wooleySourcePolynomialPhase phi alpha y)).support,
        wooleySourceTwist gamma
          (fun y => wooleySourcePolynomialPhase phi alpha y) n =
      wooleySourcePolynomialSum phi gamma alpha := by
  rw [wooleySourceTwist_support gamma _
    (fun n => wooleySourcePolynomialPhase_ne_zero phi alpha n)]
  unfold wooleySourcePolynomialSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [wooleySourceTwist_apply]

/-- At zero Fourier frequency a normalized polynomial sum is just the
normalized ordinary sum of its coefficients. -/
theorem wooleySourceNormalizedPolynomialSum_zero
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) :
    wooleySourceNormalizedPolynomialSum phi gamma
        (0 : Fin k → ZMod q) =
      if wooleySourceMassSq gamma = 0 then 0
      else ((Real.sqrt (wooleySourceMassSq gamma) : ℂ)⁻¹) *
        ∑ n ∈ gamma.support, gamma n := by
  unfold wooleySourceNormalizedPolynomialSum wooleySourcePolynomialSum
  split_ifs
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [wooleySourcePolynomialPhase_zero, mul_one]

#print axioms wooleySourceTwist_apply
#print axioms wooleySourceTwist_support
#print axioms wooleySourceMassSq_twist
#print axioms wooleySourceResidueMassSq_twist
#print axioms WooleySourceSequence.Admissible.twist
#print axioms wooleySourcePolynomialPhase_norm
#print axioms wooleySourcePolynomialPhase_ne_zero
#print axioms wooleySourcePolynomialPhase_zero
#print axioms wooleySource_sum_twist_eq_polynomialSum
#print axioms wooleySourceNormalizedPolynomialSum_zero

end

end GafniTao
