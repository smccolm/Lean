import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic

/-! A degree-at-most-two integral element satisfies a monic quadratic relation
over the actual polynomial coordinate ring. This is the coefficient-ring step
used for the odd Velu y-coordinate; its hypotheses will be discharged by the
actual translation fixed field and the already proved coordinate integrality.
Adapted from the quadratic-relation argument in TauCeti Isogeny/Velu/Equation.lean,
Apache-2.0, commit bfcff79b60964ba7bdb78b952828313686c327ba. The degree bound
is sufficient: multiplying the minimal polynomial by a power of X gives
a monic polynomial of degree exactly two without assuming nonrationality. -/

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace Dubon2026.SourceEllipticFunctionField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An integral element of degree at most two over F(x) has a monic quadratic relation over F[x]. -/
theorem exists_quadratic_relation_of_integral {x y : E}
    (hx : Transcendental F x) (hy : IsIntegral (Algebra.adjoin F {x}) y)
    (hd : (minpoly F⟮x⟯ y).natDegree ≤ 2) :
    ∃ p q : F[X], y ^ 2 + aeval x p * y + aeval x q = 0 := by
  let R := Algebra.adjoin F {x}
  haveI : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental F x hx).toRingEquiv
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' F⟮x⟯ hy
  have hdeg : (minpoly R y).natDegree ≤ 2 := by
    rw [hmap, Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective R F⟮x⟯)] at hd
    exact hd
  let m : R[X] := minpoly R y * X ^ (2 - (minpoly R y).natDegree)
  have hm : m.Monic := (minpoly.monic hy).mul (monic_X_pow _)
  have hmd : m.natDegree = 2 := by
    dsimp only [m]
    rw [(minpoly.monic hy).natDegree_mul (monic_X_pow _), natDegree_X_pow]
    change (minpoly R y).natDegree + (2 - (minpoly R y).natDegree) = 2
    omega
  have hmy : aeval y m = 0 := by
    simp only [m, map_mul, minpoly.aeval, zero_mul]
  obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval F x (m.coeff 1).2
  obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval F x (m.coeff 0).2
  refine ⟨p, q, ?_⟩
  rw [Polynomial.aeval_eq_sum_range, hmd] at hmy
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at hmy
  rw [← hmd, hm.coeff_natDegree, hmd] at hmy
  rw [hp, hq]
  simpa [Algebra.smul_def, add_comm, add_left_comm, add_assoc] using hmy

end Dubon2026.SourceEllipticFunctionField
