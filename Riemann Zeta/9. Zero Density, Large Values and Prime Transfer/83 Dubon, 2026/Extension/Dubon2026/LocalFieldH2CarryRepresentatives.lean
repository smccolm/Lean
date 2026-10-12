import Dubon2026.LocalFieldPeriodH2Equiv

/-! # Actual carry representatives cover every original unramified local H2 class -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

/-- Every original continuous unramified local H2 class has a genuine
carry representative using the actual arithmetic Frobenius and an actual
base-field unit. The original degree-one case is included. -/
theorem localFieldH2_exists_carry_representative
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    ∃ u : Kˣ, Submodule.Quotient.mk (galoisUnitCarryCocycle
      (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) u) = x := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  by_cases hn : 1 < Nat.card Gal(L/K)
  · obtain ⟨u, hu⟩ := localFieldUnitOrder_surjective K
      ((localFieldPeriodH2Equiv K L x).val : ℤ)
    refine ⟨u.toMul, (localFieldPeriodH2Equiv K L).injective ?_⟩
    rw [localFieldPeriodH2Equiv_mk, galoisUnitCarryCocycle_period _ _ _ hn,
      ofMul_toMul, hu,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hdegree : Module.finrank K L = 1 := by
      have hp : 0 < Nat.card Gal(L/K) := Nat.card_pos
      rw [← IsGalois.card_aut_eq_finrank]
      omega
    haveI : Subsingleton (ZMod (Module.finrank K L)) := by
      rw [hdegree]
      infer_instance
    exact ⟨1, (localFieldPeriodH2Equiv K L).injective (Subsingleton.elim _ _)⟩

end
end Dubon2026
