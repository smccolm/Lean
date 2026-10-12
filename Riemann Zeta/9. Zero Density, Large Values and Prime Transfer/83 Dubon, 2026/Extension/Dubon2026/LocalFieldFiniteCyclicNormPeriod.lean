import Dubon2026.LocalFieldFiniteStageFundamentalClass
import Dubon2026.CyclicGaloisH2PeriodSurjective

/-! # The actual period equivalence for every finite cyclic local extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- The original cyclic cocycle period in the original base-unit
quotient by genuine field-unit norms. -/
def localFieldFiniteCyclicNormPeriod :
    GaloisUnitH2FiniteStage K Ω E →ₗ[ℤ]
      (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := E))) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact cyclicGaloisH2PeriodNormMap g hg

omit [IsGalois K Ω] [IsSepClosed Ω] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] in
/-- Actual period classes exhaust the actual norm quotient for every
cyclic local extension, including ramified extensions. -/
theorem localFieldFiniteCyclicNormPeriod_surjective :
    Function.Surjective (localFieldFiniteCyclicNormPeriod K Ω E g hg) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact cyclicGaloisH2PeriodNormMap_surjective g hg

/-- The period map is an actual equivalence. Finiteness is proved
from the full local invariant, not assumed for the original norm quotient. -/
theorem localFieldFiniteCyclicNormPeriod_bijective :
    Function.Bijective (localFieldFiniteCyclicNormPeriod K Ω E g hg) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  haveI : Finite (GaloisUnitH2FiniteStage K Ω E) :=
    Finite.of_equiv (ZMod (Module.finrank K E))
      (localFieldFiniteStageH2CyclicEquiv K Ω E).symm.toEquiv
  haveI : Finite (Additive Kˣ ⧸ LinearMap.range
      (galoisUnitFieldNormLinear (K := K) (L := E))) :=
    Finite.of_surjective _ (localFieldFiniteCyclicNormPeriod_surjective K Ω E g hg)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact cyclicGaloisH2PeriodNormMap_bijective g hg

/-- The genuine period equivalence keeps the literal cocycle map. -/
def localFieldFiniteCyclicNormPeriodEquiv :
    GaloisUnitH2FiniteStage K Ω E ≃ₗ[ℤ]
      (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := E))) :=
  LinearEquiv.ofBijective (localFieldFiniteCyclicNormPeriod K Ω E g hg)
    (localFieldFiniteCyclicNormPeriod_bijective K Ω E g hg)

/-- The exact norm index of any actual finite cyclic local extension
is its original field degree. -/
theorem localFieldFiniteCyclicNormQuotient_card :
    Nat.card (Additive Kˣ ⧸ LinearMap.range
      (galoisUnitFieldNormLinear (K := K) (L := E))) = Module.finrank K E := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  rw [← Nat.card_congr (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).toEquiv]
  exact localFieldFiniteStageH2_card K Ω E

end
end Dubon2026
