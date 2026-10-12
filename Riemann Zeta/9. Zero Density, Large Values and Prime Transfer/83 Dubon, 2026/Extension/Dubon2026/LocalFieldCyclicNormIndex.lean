import Dubon2026.LocalFieldCyclicSecondCohomologyOrder
import Dubon2026.ContinuousCyclicGaloisNormQuotient

/-! # The original cyclic local field norm quotient and its exact order -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel
attribute [local instance] IsCyclic.commGroup

/-- The quotient of actual base-field units by actual extension-field norms
is finite, with order the original cyclic Galois group order. The existing
continuous norm-quotient equivalence is composed with the genuine discrete
comparison and the proved local cohomology order. -/
theorem localField_cyclic_norm_quotient_order
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Finite (Additive Kˣ ⧸ (galoisUnitFieldNormLinear (K := K) (L := L)).range) ∧
      Nat.card (Additive Kˣ ⧸ (galoisUnitFieldNormLinear (K := K) (L := L)).range) =
        Nat.card Gal(L/K) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e := (continuousCyclicGaloisNormQuotientEquiv g hg).trans
    (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := L)))
  obtain ⟨hfinite, hcard⟩ := localField_cyclic_second_cohomology_order K L
  haveI : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := hfinite
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, (Nat.card_congr e.toEquiv).trans hcard⟩

/-- The original cyclic local norm quotient has precisely the extension
degree as its order, using the genuine Galois group cardinality theorem. -/
theorem localField_cyclic_norm_index
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Nat.card (Additive Kˣ ⧸ (galoisUnitFieldNormLinear (K := K) (L := L)).range) =
      Module.finrank K L := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  exact (localField_cyclic_norm_quotient_order K L).2.trans
    (IsGalois.card_aut_eq_finrank K L)

end
end Dubon2026
