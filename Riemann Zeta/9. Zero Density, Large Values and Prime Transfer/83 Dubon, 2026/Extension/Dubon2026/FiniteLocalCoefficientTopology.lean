import Dubon2026.FiniteNilpotentAdicCoefficients
import Mathlib.RingTheory.HopkinsLevitzki

/-! # The actual maximal-adic topology and completeness of finite local coefficient rings -/

namespace Dubon2026
noncomputable section

variable (R : Type*) [CommRing R] [IsLocalRing R] [Finite R]

/-- The genuine maximal ideal of each original finite local coefficient ring is nilpotent. -/
theorem finiteLocalCoefficient_maximal_nilpotent :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n = ⊥ := by
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp
    (isArtinian_of_finite (R := R) (M := R))

/-- An actual maximal-adic original finite local coefficient ring is discrete. -/
theorem finiteLocalCoefficient_discrete [WithIdeal R]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R) : DiscreteTopology R := by
  obtain ⟨n, hn⟩ := finiteLocalCoefficient_maximal_nilpotent R
  exact nilpotentAdic_discreteTopology n (by rw [hR]; exact hn)

/-- The original finite local coefficient ring is genuinely complete and separated for its actual maximal ideal. -/
theorem finiteLocalCoefficient_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  obtain ⟨n, hn⟩ := finiteLocalCoefficient_maximal_nilpotent R
  exact finiteRing_nilpotentIdeal_isAdicComplete _ n hn

/-- The topology defined by powers of the actual original maximal ideal is the discrete topology. -/
theorem finiteLocalCoefficient_adicTopology_eq_bot :
    (IsLocalRing.maximalIdeal R).adicTopology = ⊥ := by
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  letI : DiscreteTopology R := finiteLocalCoefficient_discrete R rfl
  exact DiscreteTopology.eq_bot

end
end Dubon2026
