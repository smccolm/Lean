import Dubon2026.OriginalCoinducedGlobalDimensionShift
import Dubon2026.CoinducedCosetTrace
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual coefficient norms vanish in positive cohomology

The degree-two norm criterion in DUB-17's finite class/Ext argument uses
the sum of conjugates of an integral linear map. Factor that literal sum
through original coinduced functions and the genuine coset trace. Existing
Shapiro vanishing proves its positive cohomology map is zero. The converse
norm criterion for the arithmetic class coefficient remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (A C : Rep.{0} ℤ G)

/-- An original integral coefficient map is equivariant after restriction to the actual trivial subgroup. -/
def originalTrivialSubgroupCoefficientMap (η : A →ₗ[ℤ] C) :
    Rep.res (⊥ : Subgroup G).subtype A ⟶ Rep.res (⊥ : Subgroup G).subtype C :=
  Rep.ofHom ⟨η, by
    intro g
    have hg : (g : G) = 1 := g.property
    apply LinearMap.ext
    intro x
    change η (A.ρ (g : G) x) = C.ρ (g : G) (η x)
    rw [hg, map_one, map_one]
    rfl⟩

variable [Fintype G]

/-- The original coefficient norm is the actual coinduction unit, coefficient map and coset trace. -/
def originalCoefficientNormMorphism (η : A →ₗ[ℤ] C) : A ⟶ C :=
  letI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  originalCoinducedUnit A ≫
    (Rep.coindFunctor ℤ (⊥ : Subgroup G).subtype).map
      (originalTrivialSubgroupCoefficientMap A C η) ≫
    coinducedCosetTrace C (⊥ : Subgroup G)

/-- The genuine coefficient norm is exactly the sum of conjugates used by the source relation-extension argument. -/
theorem originalCoefficientNormMorphism_apply (η : A →ₗ[ℤ] C) (x : A) :
    (originalCoefficientNormMorphism A C η).hom x =
      ∑ g : G, C.ρ g (η (A.ρ g⁻¹ x)) := by
  letI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  change (∑ q : G ⧸ (⊥ : Subgroup G), coinducedCosetValues C (⊥ : Subgroup G)
    (((Rep.coindFunctor ℤ (⊥ : Subgroup G).subtype).map
      (originalTrivialSubgroupCoefficientMap A C η)).hom ((originalCoinducedUnit A).hom x)) q) = _
  refine Fintype.sum_equiv (QuotientGroup.quotientBot.toEquiv) _ _ ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H g => rfl

/-- Every positive-degree cohomology map induced by the actual coefficient norm vanishes through the proved original coinduced acyclicity. -/
theorem originalCoefficientNormMorphism_positive_map_zero (η : A →ₗ[ℤ] C) (n : ℕ) :
    (groupCohomology.functor ℤ G (n + 1)).map (originalCoefficientNormMorphism A C η) = 0 := by
  letI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  have hz : (groupCohomology.functor ℤ G (n + 1)).map (originalCoinducedUnit A) = 0 :=
    (originalCoinducedFunction_positive_zero A n).eq_zero_of_tgt _
  unfold originalCoefficientNormMorphism
  erw [Functor.map_comp, hz, Limits.zero_comp]

end
end Dubon2026
