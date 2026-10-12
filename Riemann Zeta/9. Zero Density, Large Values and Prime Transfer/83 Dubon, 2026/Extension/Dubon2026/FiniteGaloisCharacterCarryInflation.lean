import Dubon2026.LocalFieldFiniteCyclicCarryInvariant

/-! # Genuine finite-field inflation preserves actual character carry classes -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- Actual original character carry classes commute with genuine
finite-stage inflation. The character is precomposed with the literal
restriction of original automorphisms, and the base unit is unchanged. -/
theorem localFieldFiniteCharacterCarryClass_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      localFieldFiniteCharacterCarryClass K Ω F
        (χ.comp (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))) u := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  change finiteGaloisUnitTowerH2Inflation K E F
    (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) = _
  rw [finiteGaloisUnitTowerH2Inflation_mk]
  congr 1

end
end Dubon2026
