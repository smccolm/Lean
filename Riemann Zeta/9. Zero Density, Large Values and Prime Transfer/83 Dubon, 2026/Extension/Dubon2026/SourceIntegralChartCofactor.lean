import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
equality of total chart orders. A nonzero integral function has an integral
cofactor whose product lies in the base ring. Native algebraic cofactor
existence and finite generated-adjoin integrality replace the external
polynomial degree induction. This will reduce total-order equality to the
normalized linear factors of a polynomial in the separating coordinate. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section

theorem exists_integral_cofactor
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S] [Algebra R S]
    {f : S} (hf0 : f ≠ 0) (hfi : IsIntegral R f) :
    ∃ g : S, IsIntegral R g ∧ ∃ c : R, c ≠ 0 ∧ f * g = algebraMap R S c := by
  obtain ⟨g, hg, c, hc, hfg⟩ := hfi.isAlgebraic.exists_nonzero_eq_adjoin_mul
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf0)
  exact ⟨g, IsIntegral.of_mem_of_fg _ (IsIntegral.fg_adjoin_singleton hfi) _ hg, c, hc, hfg⟩

end
end Dubon2026.SourceCurve.RegularProlongation
