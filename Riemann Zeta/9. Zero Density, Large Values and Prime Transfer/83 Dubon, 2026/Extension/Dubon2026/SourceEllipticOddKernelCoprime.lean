import Dubon2026.SourceEllipticOddNormCoordinates
import Mathlib.RingTheory.Coprime.Lemmas

/-! No cancellation occurs in the odd quotient x-coordinate.
Evaluating its actual cleared numerator at each kernel abscissa leaves one
nonzero term. This is the coprimality input to the exact rational-function degree,
then the odd quotient field embedding and cyclic modular-polynomial roots
required on the DUB-17/18 dependency chain. -/

open Polynomial Finset

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

variable {F : Type*} [Field F]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → F)

/-- At a kernel abscissa only its own summand survives in the cleared numerator. -/
theorem AP_eval_kernel {q : ι} (hq : q ∈ S) :
    (AP S x t u).eval (x q) = u q * ∏ j ∈ S.erase q, (x q - x j) ^ 2 := by
  have hh : (hP S x).eval (x q) = 0 := by
    rw [hP_eval]
    exact Finset.prod_eq_zero hq (sub_self _)
  have hz {i : ι} (hiq : i ≠ q) : ∏ j ∈ S.erase i, (x q - x j) ^ 2 = 0 :=
    Finset.prod_eq_zero (mem_erase.mpr ⟨hiq.symm, hq⟩) (by simp)
  have hs : (∑ i ∈ S, (t i * (x q - x i) + u i) *
      ∏ j ∈ S.erase i, (x q - x j) ^ 2) = u q * ∏ j ∈ S.erase q, (x q - x j) ^ 2 := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro i _ hiq
      rw [hz hiq, mul_zero]
    · exact fun h => (h hq).elim
  simpa [AP, eval_finsetSum, eval_prod, hh] using hs

/-- Distinct kernel abscissae and nonzero tangent-square terms prevent numerator vanishing. -/
theorem AP_eval_kernel_ne_zero (hx : Set.InjOn x (S : Set ι))
    (hu : ∀ q ∈ S, u q ≠ 0) {q : ι} (hq : q ∈ S) :
    (AP S x t u).eval (x q) ≠ 0 := by
  rw [AP_eval_kernel S x t u hq]
  refine mul_ne_zero (hu q hq) (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
  obtain ⟨hjq, hj⟩ := mem_erase.mp hj
  exact pow_ne_zero 2 (sub_ne_zero.mpr fun h => hjq (hx hj hq h.symm))

/-- The cleared numerator is coprime to the squared kernel denominator. -/
theorem isCoprime_AP_hP_sq (hx : Set.InjOn x (S : Set ι))
    (hu : ∀ q ∈ S, u q ≠ 0) : IsCoprime (AP S x t u) (hP S x ^ 2) := by
  apply IsCoprime.pow_right
  rw [hP]
  apply IsCoprime.prod_right
  intro q hq
  have hd : ¬(X - C (x q) ∣ AP S x t u) := by
    rw [dvd_iff_isRoot]
    exact AP_eval_kernel_ne_zero S x t u hx hu hq
  exact ((irreducible_X_sub_C (x q)).isCoprime_or_dvd (AP S x t u)).resolve_right hd |>.symm

end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
