import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # The integral finite adeles and their original arithmetic intersection

This is the finite-place input for discreteness of principal number-field
adeles, needed for finite arithmetic stabilizers in the DUB-17 unitary
small-level argument. It extends the repository's rational intersection
proof by reusing the same pinned Dedekind valuation theorem.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Finite adeles integral in every original completed valuation ring. -/
def numberFieldIntegralFiniteAdeles : Subring (FiniteAdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers K}
  zero_mem' := fun v => (v.adicCompletionIntegers K).zero_mem
  one_mem' := fun v => (v.adicCompletionIntegers K).one_mem
  add_mem' hx hy v := (v.adicCompletionIntegers K).toSubring.add_mem (hx v) (hy v)
  mul_mem' hx hy v := (v.adicCompletionIntegers K).toSubring.mul_mem (hx v) (hy v)
  neg_mem' hx v := (v.adicCompletionIntegers K).toSubring.neg_mem (hx v)

/-- The integral product is open in the original restricted-product topology. -/
theorem numberFieldIntegralFiniteAdeles_isOpen :
    IsOpen (numberFieldIntegralFiniteAdeles K : Set (FiniteAdeleRing (𝓞 K) K)) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- A principal finite adele is integral exactly when its original number-field element is integral. -/
theorem numberFieldFiniteAdele_integral_iff (x : K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ numberFieldIntegralFiniteAdeles K ↔
      IsIntegral ℤ x := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K x (by
      intro v
      have hv := h v
      change Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 at hv
      simpa only [algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hv)
    rw [← hn]
    exact n.property
  · intro hx
    let n : 𝓞 K := ⟨x, hx⟩
    intro v
    change Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1
    simpa only [algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using
      (v.valuation_le_one (K := K) n)

end
end Dubon2026
