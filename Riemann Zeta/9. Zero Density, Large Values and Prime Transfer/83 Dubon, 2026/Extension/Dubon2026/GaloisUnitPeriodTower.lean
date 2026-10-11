import Dubon2026.RepresentationPeriodInflation
import Dubon2026.FiniteGaloisUnitTowerInflation
import Dubon2026.GaloisUnitCyclicPeriodBase
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Literal base-unit periods of original cyclic Galois cocycles under actual tower inflation -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
  (h : Gal(M/K)) (hh : ∀ x, x ∈ Subgroup.zpowers h)

/-- For actual compatible original generators, the original inflated
cocycle's base-unit period is exactly the relative extension degree times
the original lower period. All cochain and coefficient maps are literal. -/
theorem galoisUnitCyclicPeriodBase_tower
    (hrestrict : AlgEquiv.restrictNormalHom L h = g)
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase h hh (finiteGaloisUnitTowerCocycleInflation K L M c) =
      Module.finrank L M • galoisUnitCyclicPeriodBase g hg c := by
  let j := (finiteGaloisUnitTowerInclusion K L M).hom.toLinearMap
  let bL : Additive Kˣ →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K L :=
    (Units.map (algebraMap K L).toMonoidHom).toAdditive.toIntLinearMap
  let bM : Additive Kˣ →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K M :=
    (Units.map (algebraMap K M).toMonoidHom).toAdditive.toIntLinearMap
  have hb (u : Additive Kˣ) : j (bL u) = bM u := by
    apply Additive.toMul.injective
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply K L M u.toMul.val).symm
  have horder : orderOf h = orderOf g * Module.finrank L M := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hh,
      orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank,
      IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have hperiod := representationCyclicPeriod_inflation
    (Rep.ofAlgebraAutOnUnits K L) (Rep.ofAlgebraAutOnUnits K M)
    (AlgEquiv.restrictNormalHom L) j g h hrestrict (orderOf g)
    (pow_orderOf_eq_one g) (Module.finrank L M) c.val
  apply Additive.toMul.injective
  apply galoisUnitsBaseCoefficient_injective (L := M)
  rw [galoisUnitCyclicPeriodBase_coefficient]
  change representationCyclicTwoCochainPeriodSum (Rep.ofAlgebraAutOnUnits K M)
      h (orderOf h) (fun p => j (c.val
        (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))) =
    bM (Module.finrank L M • galoisUnitCyclicPeriodBase g hg c)
  rw [horder, hperiod, map_nsmul, ← hb]
  congr 1
  exact congrArg j (galoisUnitCyclicPeriodBase_coefficient g hg c).symm

end
end Dubon2026
