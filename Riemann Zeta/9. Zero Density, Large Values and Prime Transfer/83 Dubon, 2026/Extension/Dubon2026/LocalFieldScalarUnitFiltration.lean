import Dubon2026.ScalarLatticeFiltration
import Dubon2026.LocalFieldNormalLatticeUnits

/-! # Actual compact Galois-stable unit subgroups at every original scalar level -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- A genuine original small lattice gives an actual nested compact unit
filtration at every scalar power. Product closure, inverse closure, the exact
carrier and the original Galois action are all constructed. -/
theorem localField_exists_scalar_unit_filtration
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (A : Submodule 𝒪[K] L) (hA : A.FG) (π : 𝒪[K])
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ scalarLatticeImage A π)
    (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A) :
    ∃ U : ℕ → Subgroup Lˣ, ∀ j,
      IsCompact (U j : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ j)) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
      U (j + 1) ≤ U j := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  have hex (j : ℕ) : ∃ U : Subgroup Lˣ, IsCompact (U : Set Lˣ) ∧
      ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ j) := by
    let B := scalarLatticeImage A (π ^ j)
    have hB : IsCompact (B : Set L) :=
      localField_finite_lattice_isCompact K L B (hA.map _)
    have hm : ∀ x ∈ B.toAddSubgroup, ∀ y ∈ B.toAddSubgroup, x * y ∈ B.toAddSubgroup := by
      intro x hx y hy
      exact scalarLatticeImage_le B π (scalarLatticeImage_level_product_gain A π hmul j hx hy)
    have hn : ∀ x ∈ B.toAddSubgroup, (1 : L) + x ≠ 0 := by
      intro x hx
      exact hunit x (scalarLatticeImage_le A (π ^ j) hx)
    let M := latticeUnitSubmonoid B.toAddSubgroup hm
    have hM : IsCompact (M : Set Lˣ) :=
      latticeUnitSubmonoid_isCompact B.toAddSubgroup hm hB hn
    exact ⟨compactSubmonoidSubgroup M hM, hM, fun _ => Iff.rfl⟩
  choose U hC hU using hex
  refine ⟨U, fun j => ⟨hC j, hU j, ?_, ?_⟩⟩
  · intro σ u hu
    apply (hU j _).mpr
    have h := scalarLatticeImage_galois_stable 𝒪[K] K L A hstable (π ^ j) σ
      ((hU j u).mp hu)
    simpa only [map_sub, map_one, Units.coe_map] using h
  · intro u hu
    exact (hU j u).mpr (scalarLatticeImage_pow_succ_le A π j ((hU (j + 1) u).mp hu))

end
end Dubon2026
