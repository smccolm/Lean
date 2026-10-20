import Dubon2026.NumberFieldPositiveIntegralMultiple
import Mathlib.RingTheory.Trace.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! # A fixed denominator for the original number-field trace dual

The native trace-dual basis gives one positive integer that makes any
element with integral traces against all algebraic integers integral.
This supplies the uniform dual-lattice containment needed to bound the
Gram determinants in DUB-17's actual arithmetic double-coset argument.
It avoids introducing a new semilocal tensor comparison assumption.
-/

namespace Dubon2026

noncomputable section

open NumberField

/-- A fixed positive integer clears the original trace dual of the ring of integers. -/
theorem numberField_exists_trace_dual_denominator
    (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℤ, 0 < c ∧ ∀ x : K,
      (∀ a : 𝓞 K, IsIntegral ℤ (Algebra.trace ℚ K (x * (a : K)))) →
        IsIntegral ℤ (c • x) := by
  classical
  let b := integralBasis K
  obtain ⟨c, hc, hint⟩ := numberField_exists_positive_integral_multiple b.traceDual
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hcoeff (i) : IsIntegral ℤ (b.traceDual.repr x i) := by
    rw [Module.Basis.traceDual_repr_apply]
    change IsIntegral ℤ (Algebra.trace ℚ K (x * b i))
    simpa only [b, integralBasis_apply] using hx (RingOfIntegers.basis K i)
  rw [← b.traceDual.sum_repr x, Finset.smul_sum]
  apply IsIntegral.sum
  intro i _
  rw [smul_comm]
  rw [Algebra.smul_def]
  exact (hcoeff i).algebraMap.mul (hint i)

end
end Dubon2026
