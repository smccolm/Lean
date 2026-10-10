import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DualNumber
import Mathlib.Topology.UniformSpace.Compact

/-! # Genuine adic completeness of finite coefficients with nilpotent maximal ideal -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R]

/-- A nilpotent original defining ideal gives the discrete topology on the original adic coefficient ring. -/
theorem nilpotentAdic_discreteTopology [WithIdeal R]
    (n : ℕ) (hn : (WithIdeal.i : Ideal R) ^ n = ⊥) : DiscreteTopology R := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  simpa only [hn, Submodule.bot_coe] using
    (isAdic_iff.mp (rfl : IsAdic (WithIdeal.i : Ideal R))).1 n

/-- Every actual finite coefficient ring is complete for any original nilpotent ideal. Both completeness and separation are derived from its genuine adic topology. -/
theorem finiteRing_nilpotentIdeal_isAdicComplete [Finite R]
    (I : Ideal R) (n : ℕ) (hn : I ^ n = ⊥) : IsAdicComplete I R := by
  letI : WithIdeal R := ⟨I⟩
  letI : DiscreteTopology R := nilpotentAdic_discreteTopology n hn
  exact (IsAdic.isAdicComplete_iff (rfl : IsAdic I)).mpr ⟨inferInstance, inferInstance⟩

/-- The maximal ideal of the original dual-number algebra over a field has square zero. -/
theorem dualNumber_maximalIdeal_sq_zero (K : Type*) [Field K] :
    IsLocalRing.maximalIdeal (DualNumber K) ^ 2 = ⊥ := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow,
    DualNumber.eps_pow_two, Ideal.span_singleton_zero]

/-- The actual dual-number coefficient algebra over a finite field is complete for its original maximal ideal. -/
theorem finiteDualNumber_maximal_isAdicComplete (K : Type*) [Field K] [Finite K] :
    IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber K)) (DualNumber K) := by
  letI : Finite (DualNumber K) := inferInstanceAs (Finite (K × K))
  exact finiteRing_nilpotentIdeal_isAdicComplete _ 2 (dualNumber_maximalIdeal_sq_zero K)

end
end Dubon2026
