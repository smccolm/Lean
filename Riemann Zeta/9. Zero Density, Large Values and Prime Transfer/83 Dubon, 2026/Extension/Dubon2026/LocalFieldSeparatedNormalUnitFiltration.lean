import Dubon2026.LocalFieldScalarUnitFiltration
import Dubon2026.ScalarLatticeFiltrationSeparation
import Dubon2026.LocalFieldCompleteNormalLattice

/-! # The original normal lattice gives a separating compact Galois unit filtration -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Construct the actual compact nested Galois unit filtration from one
original integral normal basis. Its exact scalar carriers and separation are
derived from the same original lattice and its proved adic completeness. -/
theorem localField_exists_separated_normal_unit_filtration
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : ℕ → Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ j, IsCompact (U j : Set Lˣ) ∧
        (∀ u : Lˣ, u ∈ U j ↔ (u : L) - 1 ∈
          scalarLatticeImage
            (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
            (π ^ j)) ∧
        (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
          Units.map (σ : L →+* L).toMonoidHom u ∈ U j) ∧
        U (j + 1) ≤ U j) ∧
      ∀ u : Lˣ, (∀ j, u ∈ U j) → u = 1 := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  obtain ⟨b, hb, n, hu, hl, hcomplete, _, _⟩ :=
    localField_exists_complete_normal_lattice K L π hπ
  let A := Submodule.span 𝒪[K] (Set.range b)
  let B := scalarLatticeImage A (π ^ (n + 1))
  have hA : A.FG := Submodule.fg_span (Set.finite_range b)
  have hB : B.FG := hA.map _
  have hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ scalarLatticeImage B π := by
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := scalarLatticeImage_product_gain A
      (ValuativeRel.valuation L).integer π n hu (fun a ha => hl ⟨a, ha⟩) hx hy
    exact (mem_scalarLatticeImage B π (x * y)).mpr ⟨z, hz, he.symm⟩
  have hunit : ∀ x ∈ B, (1 : L) + x ≠ 0 := by
    intro x hx
    exact localField_scaled_lattice_one_add_ne_zero K L A π hπ.not_isUnit n hu hx
  have hstable : ∀ σ : Gal(L/K), ∀ x ∈ B, σ x ∈ B := by
    intro σ x hx
    exact scalarLatticeImage_galois_stable 𝒪[K] K L A
      (fun τ _ ha => normalBasis_span_galois_stable 𝒪[K] K L b hb τ ha)
      (π ^ (n + 1)) σ hx
  obtain ⟨U, hU⟩ := localField_exists_scalar_unit_filtration K L B hB π hmul hunit hstable
  refine ⟨b, n, U, hb, hu, hl, hU, ?_⟩
  intro u huU
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) A := hcomplete
  have hz : (u : L) - 1 = 0 :=
    scalarLatticeImage_separated_of_isHausdorff A (IsLocalRing.maximalIdeal 𝒪[K]) π
      (by simpa using hπ.not_isUnit) ((u : L) - 1) (fun j =>
        scalarLatticeImage_mono B A (scalarLatticeImage_le A (π ^ (n + 1)))
          (π ^ j) ((hU j).2.1 u |>.mp (huU j)))
  exact Units.ext (sub_eq_zero.mp hz)

end
end Dubon2026
