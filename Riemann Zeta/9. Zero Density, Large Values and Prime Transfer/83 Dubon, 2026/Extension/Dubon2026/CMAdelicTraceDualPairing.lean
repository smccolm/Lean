import Dubon2026.NumberFieldTraceDualDenominator
import Dubon2026.CMAdelicLatticeIntegralTraceForm

/-! # Integral Hermitian pairings from the actual trace-dual condition

The attached lattice is a module over the original ring of integers.
Testing its trace-dual condition on every integral scalar multiple and
using the fixed trace-dual denominator converts that condition to
integrality of the original Hermitian pairing. This serves the uniform
dual-lattice containment in DUB-17's determinant bound.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integral scalar multiples test the actual number-field trace dual of each pairing. -/
theorem cmAdelicTraceDual_pairing_test (H : Matrix ι ι K) (d : ℤ)
    (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K)
    (hx : ∀ y : numberFieldAdelicLattice K ι g.val,
      IsIntegral ℤ (d • cmHermitianRationalTraceForm K H x y.val))
    (y : numberFieldAdelicLattice K ι g.val) (a : 𝓞 K) :
    IsIntegral ℤ (Algebra.trace ℚ K
      ((d • dotProduct (star x) (H.mulVec y.val)) * (a : K))) := by
  have h := hx (a • y)
  change IsIntegral ℤ (d • Algebra.trace ℚ K
    (dotProduct (star x) (H.mulVec ((a : K) • y.val)))) at h
  rw [mulVec_smul, dotProduct_smul,
    ← (Algebra.trace ℚ K).map_smul_of_tower] at h
  convert h using 1
  congr 1
  simp only [zsmul_eq_mul, smul_eq_mul]
  ring

/-- One fixed number-field denominator converts every actual trace-dual condition to integral Hermitian pairings. -/
theorem cmAdelicTraceDual_exists_uniform_pairing_denominator :
    ∃ c : ℤ, 0 < c ∧ ∀ (H : Matrix ι ι K) (d : ℤ)
      (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K),
      (∀ y : numberFieldAdelicLattice K ι g.val,
        IsIntegral ℤ (d • cmHermitianRationalTraceForm K H x y.val)) →
      ∀ y : numberFieldAdelicLattice K ι g.val,
        IsIntegral ℤ ((c * d) • dotProduct (star x) (H.mulVec y.val)) := by
  obtain ⟨c, hc, htrace⟩ := numberField_exists_trace_dual_denominator K
  refine ⟨c, hc, ?_⟩
  intro H d g x hx y
  have h := htrace (d • dotProduct (star x) (H.mulVec y.val))
    (cmAdelicTraceDual_pairing_test K H d g x hx y)
  simpa only [smul_smul] using h

end
end Dubon2026
