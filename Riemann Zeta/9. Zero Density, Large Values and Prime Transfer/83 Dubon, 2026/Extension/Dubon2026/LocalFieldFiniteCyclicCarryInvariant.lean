import Dubon2026.LocalFieldFiniteCyclicNormResidue
import Dubon2026.GaloisUnitCharacterCarryPeriod

/-! # Original finite character carries and the normalized local invariant -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (E : FiniteGaloisIntermediateField K Ω)

/-- The cohomology class of the actual original finite character carry
cocycle with the actual original base-unit coefficient. -/
def localFieldFiniteCharacterCarryClass {n : ℕ} [NeZero n]
    (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) : GaloisUnitH2FiniteStage K Ω E := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)

variable [IsGalois K Ω] [IsSepClosed Ω] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- The actual finite character carry class is the exact integer carry
sum times the inverse-period image of the original base-unit norm class. -/
theorem localFieldFiniteCharacterCarryClass_eq_period
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldFiniteCharacterCarryClass K Ω E χ u =
      (∑ i ∈ Finset.range (orderOf g),
        zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) •
          (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm
            (Submodule.Quotient.mk (Additive.ofMul u)) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  apply (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).injective
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  change cyclicGaloisH2PeriodNormMap g hg
    (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) = _
  rw [cyclicGaloisH2PeriodNormMap_mk, galoisUnitCharacterCarryCocycle_period]
  exact map_nsmul (LinearMap.range
    (galoisUnitFieldNormLinear (K := K) (L := E))).mkQ _ _

/-- The normalized original invariant of the actual finite character
carry is its genuine carry sum times the invariant of the period class. -/
theorem localFieldFiniteCharacterCarryClass_invariant
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    localFieldFiniteStageInvariant K Ω E (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      (∑ i ∈ Finset.range (orderOf g),
        zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) •
          rationalCyclicInvariant (Module.finrank K E)
            (localFieldFiniteStageH2CyclicEquiv K Ω E
              ((localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm
                (Submodule.Quotient.mk (Additive.ofMul u)))) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [localFieldFiniteCharacterCarryClass_eq_period K Ω E g hg, map_nsmul,
    localFieldFiniteStageH2CyclicEquiv_invariant]

end
end Dubon2026
