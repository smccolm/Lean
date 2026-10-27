import Dubon2026.SourceFrickeFixedFieldJV3
import Dubon2026.SourceAnalyticJSurjectivity
import Mathlib.RingTheory.Algebraic.Basic

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite
Gamma1 characters -> Picard/H1 comparison -> cusp differential realization ->
rational Fourier structure -> integral descent through transcendental constants.
The existing surjectivity of the actual analytic j immediately gives polynomial
evaluation injectivity and its transcendence in the actual Fricke fraction field.
This replaces a separate cusp-asymptotic proof of the same required input.
-/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField

theorem analytic_j_aeval_injective :
    Function.Injective (Polynomial.aeval JMultiplicity.jf : Polynomial ℂ → ℍ → ℂ) := by
  intro P Q h
  apply Polynomial.funext
  intro z
  obtain ⟨τ, rfl⟩ := JMultiplicity.jf_surjective z
  exact (aeval_j_apply P τ).symm.trans ((congrFun h τ).trans (aeval_j_apply Q τ))

theorem transcendental_analytic_j : Transcendental ℂ JMultiplicity.jf :=
  transcendental_iff_injective.mpr analytic_j_aeval_injective

theorem transcendental_jA (N : ℕ) : Transcendental ℂ (jA N) := by
  intro h
  exact transcendental_analytic_j (Subalgebra.isAlgebraic_iff_isAlgebraic_val.mp h)

theorem transcendental_jK (N : ℕ) [NeZero N] : Transcendental ℂ (jK N) :=
  (transcendental_algebraMap_iff (R := ℂ)
    (IsFractionRing.injective ↥(levelRing N) (levelField N))).mpr (transcendental_jA N)

end
end Dubon2026.SourceFricke
