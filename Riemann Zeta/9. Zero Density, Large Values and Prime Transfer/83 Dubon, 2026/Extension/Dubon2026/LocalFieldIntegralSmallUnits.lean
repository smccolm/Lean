import Dubon2026.SubringUnitSubgroupEquiv
import Dubon2026.LocalFieldSmallLatticeUnits

/-! # Literal integral-unit realization of the original small-unit subgroup -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] in
/-- The actual original integer-ring scalar action stays in the actual
extension integer ring, by its literal coefficient inclusion and scalar tower. -/
theorem localField_scalar_integer_mem (r : 𝒪[K]) (a : L)
    (ha : a ∈ (ValuativeRel.valuation L).integer) :
    r • a ∈ (ValuativeRel.valuation L).integer := by
  let aI : 𝒪[L] := ⟨a, ha⟩
  have h := (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap.map_smul r aI
  change algebraMap 𝒪[L] L (r • aI) = r • a at h
  have hm := (r • aI).property
  change algebraMap 𝒪[L] L (r • aI) ∈ (ValuativeRel.valuation L).integer at hm
  rw [h] at hm
  exact hm

omit [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] in
/-- Every original field unit in the literal small-lattice subgroup is
integral. The same holds for its original inverse by subgroup inverse closure. -/
theorem localField_small_unit_integral
    (A : Submodule 𝒪[K] L) (r : 𝒪[K])
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (u : Lˣ) (hu : (u : L) - 1 ∈ scalarLatticeImage A r) :
    (u : L) ∈ (ValuativeRel.valuation L).integer := by
  obtain ⟨a, ha, he⟩ := (mem_scalarLatticeImage A r _).mp hu
  have hi : (u : L) - 1 ∈ (ValuativeRel.valuation L).integer :=
    he ▸ localField_scalar_integer_mem K L r a (hupper a ha)
  simpa only [sub_add_cancel] using
    (ValuativeRel.valuation L).integer.add_mem hi (ValuativeRel.valuation L).integer.one_mem

/-- The actual original small field-unit subgroup is equivalent to its
literal preimage in the actual integer units. Integrality is derived from the
original lattice upper bound, and the equivalence preserves the field values. -/
def localFieldSmallUnitIntegerEquiv
    (A : Submodule 𝒪[K] L) (r : 𝒪[K])
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (U : Subgroup Lˣ)
    (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A r) :
    U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom) ≃* U :=
  subringUnitSubgroupEquiv (ValuativeRel.valuation L).integer U
    (fun u hu => localField_small_unit_integral K L A r hupper u ((hU u).mp hu))

omit [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] in
/-- The actual integer-unit comparison keeps the original field coefficient. -/
theorem localFieldSmallUnitIntegerEquiv_coefficient
    (A : Submodule 𝒪[K] L) (r : 𝒪[K])
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (U : Subgroup Lˣ)
    (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A r)
    (v : U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) :
    (((localFieldSmallUnitIntegerEquiv K L A r hupper U hU v : U) : Lˣ) : L) =
      (((v : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
  rfl

end
end Dubon2026
