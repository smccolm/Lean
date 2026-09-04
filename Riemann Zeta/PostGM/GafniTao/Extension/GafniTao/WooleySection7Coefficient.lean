import GafniTao.WooleySourceTwist

/-!
# Wooley's Section 7 translated coefficient sequence

This file implements the literal coefficient family `c_y(alpha)` in
(7.14)--(7.16).  It is the affine pullback of the original coefficients to
`n = p^a y + xi`, twisted by the original polynomial phase.  The source's
normalization identities are proved exactly, including the zero-mass branch.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exact sequence
`c_y(alpha) = gamma_{p^a y+xi} e(psi(p^a y+xi;alpha))`
from the line following (7.14). -/
def wooleySection7Coefficient {k : ℕ}
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    WooleySourceSequence :=
  let pullback := wooleyAffinePullback gamma (p ^ a) (pow_pos hp a) xi
  let translated := wooleyAffinePolynomialSystem phi (p ^ a) xi
  wooleySourceTwist pullback
    (fun y => wooleySourcePolynomialPhase translated alpha y)

@[simp] theorem wooleySection7Coefficient_apply
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) (y : ℤ) :
    wooleySection7Coefficient phi gamma p a hp xi alpha y =
      gamma ((p ^ a : ℕ) * y + xi) *
        wooleySourcePolynomialPhase phi alpha
          ((p ^ a : ℕ) * y + xi) := by
  simp [wooleySection7Coefficient, wooleySourcePolynomialPhase_affine]

/-- The translated/twisted sequence has the original residue-class mass;
this is equation (7.15), squared to avoid an artificial square-root choice. -/
theorem wooley_equation_7_15
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    wooleySourceMassSq
        (wooleySection7Coefficient phi gamma p a hp xi alpha) =
      wooleySourceResidueMassSq gamma (p ^ a) (xi : ZMod (p ^ a)) := by
  unfold wooleySection7Coefficient
  rw [wooleySourceMassSq_twist _ _
    (fun y => wooleySourcePolynomialPhase_norm
      (wooleyAffinePolynomialSystem phi (p ^ a) xi) alpha y)]
  exact wooleySourceMassSq_affinePullback gamma (p ^ a) (pow_pos hp a) xi

/-- The coefficient sum of `c(alpha)` is the original unnormalised residue
sum.  It is the exact finite-support content of (7.14). -/
theorem wooleySection7Coefficient_sum
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    ∑ y ∈ (wooleySection7Coefficient
          phi gamma p a hp xi alpha).support,
        wooleySection7Coefficient phi gamma p a hp xi alpha y =
      wooleySourcePolynomialResidueSum phi gamma alpha
        (xi : ZMod (p ^ a)) := by
  calc
    ∑ y ∈ (wooleySection7Coefficient
          phi gamma p a hp xi alpha).support,
        wooleySection7Coefficient phi gamma p a hp xi alpha y =
      wooleySourcePolynomialSum
        (wooleyAffinePolynomialSystem phi (p ^ a) xi)
        (wooleyAffinePullback gamma (p ^ a) (pow_pos hp a) xi) alpha := by
          exact wooleySource_sum_twist_eq_polynomialSum
            (wooleyAffinePolynomialSystem phi (p ^ a) xi)
            (wooleyAffinePullback gamma (p ^ a) (pow_pos hp a) xi) alpha
    _ = wooleySourcePolynomialResidueSum phi gamma alpha
        (xi : ZMod (p ^ a)) :=
      wooleySourcePolynomialSum_affinePullback (pow_pos hp a)
        phi gamma alpha xi

/-- Equation (7.14) together with the zero-frequency specialization of
(7.16): for every auxiliary lower-degree system, `g_c(alpha,0)` is exactly
the original normalized residue sum `f_a(alpha;xi)`. -/
theorem wooley_equations_7_14_7_16
    {k r : ℕ} (phi : WooleyPolynomialSystem k)
    (psi : WooleyPolynomialSystem r) (gamma : WooleySourceSequence)
    (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q qPrime : ℕ} [NeZero q] [NeZero qPrime]
    (alpha : Fin k → ZMod q) :
    wooleySourceNormalizedPolynomialSum psi
        (wooleySection7Coefficient phi gamma p a hp xi alpha)
        (0 : Fin r → ZMod qPrime) =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
        (xi : ZMod (p ^ a)) := by
  rw [wooleySourceNormalizedPolynomialSum_zero]
  unfold wooleySourceNormalizedPolynomialResidueSum
  rw [wooley_equation_7_15, wooleySection7Coefficient_sum]

/-- Admissibility is preserved by the Section 7 coefficient construction. -/
theorem WooleySourceSequence.Admissible.section7Coefficient
    {k : ℕ} {gamma : WooleySourceSequence}
    (hgamma : gamma.Admissible) (phi : WooleyPolynomialSystem k)
    (p a : ℕ) (hp : 0 < p) (xi : ℤ)
    {q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) :
    (wooleySection7Coefficient phi gamma p a hp xi alpha).Admissible := by
  unfold wooleySection7Coefficient
  apply (hgamma.affinePullback (p ^ a) (pow_pos hp a) xi).twist
  intro y
  rw [wooleySourcePolynomialPhase_norm]

#print axioms wooleySection7Coefficient_apply
#print axioms wooley_equation_7_15
#print axioms wooleySection7Coefficient_sum
#print axioms wooley_equations_7_14_7_16
#print axioms WooleySourceSequence.Admissible.section7Coefficient

end

end GafniTao
