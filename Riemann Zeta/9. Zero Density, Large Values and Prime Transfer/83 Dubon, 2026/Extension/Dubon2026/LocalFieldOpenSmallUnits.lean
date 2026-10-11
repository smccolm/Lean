import Dubon2026.LocalFieldNormalLatticeUnits
import Dubon2026.LocalFieldOpenLattice

/-! # Original open normal-lattice units and the actual finite integer-unit quotient -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The literal unit subgroup of an original full small lattice is open
by continuity of its original difference-from-one map. -/
theorem localField_small_unit_subgroup_isOpen
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : π ≠ 0) (n : ℕ)
    (hbound : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ A)
    (U : Subgroup Lˣ)
    (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ (n + 1))) :
    IsOpen (U : Set Lˣ) := by
  have he : (U : Set Lˣ) =
      (fun u : Lˣ => (u : L) - 1) ⁻¹' (scalarLatticeImage A (π ^ (n + 1)) : Set L) := by
    ext u
    exact hU u
  rw [he]
  exact (localField_scaled_lattice_isOpen K L A π hπ n hbound).preimage
    (Units.continuous_val.sub continuous_const)

omit [Field K] [Algebra K L] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The quotient of the original extension integer units by the actual
preimage of an open field-unit subgroup is finite. Its compact ambient group
is the genuine integer-unit group, not the noncompact field-unit group. -/
theorem localField_integer_unit_quotient_finite
    (U : Subgroup Lˣ) (hU : IsOpen (U : Set Lˣ)) :
    Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  have hc : Continuous (Units.map (algebraMap 𝒪[L] L).toMonoidHom) :=
    Continuous.units_map _ continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ (hU.preimage hc)

/-- The constructed original normal lattice supplies a compact open,
Galois-stable subgroup of actual field units and a finite quotient of the
actual extension integer units. No cohomological triviality is asserted here. -/
theorem localField_exists_open_normal_lattice_unit_subgroup [IsGalois K L]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U := by
  obtain ⟨b, n, U, hb, hu, hl, hc, hU, hs⟩ :=
    localField_exists_normal_lattice_unit_subgroup K L π hπ
  have ho := localField_small_unit_subgroup_isOpen K L _ π hπ.ne_zero n hl U hU
  exact ⟨b, n, U, hb, hu, hl, hc, ho,
    localField_integer_unit_quotient_finite L U ho, hU, hs⟩

end
end Dubon2026
