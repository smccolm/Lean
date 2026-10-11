import Dubon2026.LocalFieldSmallLatticeUnits
import Dubon2026.LocalFieldIntegralNormalLattice

/-! # Actual Galois-stable compact units from the original normal lattice -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Original Galois stability is preserved by a scalar from the original
base integer ring; both the lattice and the coefficient remain literal. -/
theorem scalarLatticeImage_galois_stable
    (R K L : Type) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (A : Submodule R L) (hA : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A)
    (r : R) (σ : Gal(L/K)) {x : L} (hx : x ∈ scalarLatticeImage A r) :
    σ x ∈ scalarLatticeImage A r := by
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A r x).mp hx
  refine (mem_scalarLatticeImage A r _).mpr ⟨σ a, hA σ a ha, ?_⟩
  exact ((σ.restrictScalars R).toLinearMap.map_smul r a).symm

/-- Construct the original integral normal lattice and an actual compact
Galois-stable small-unit subgroup from it. The subgroup carrier is exactly
`1 + π^(n+1) A` inside the units of the original extension field. -/
theorem localField_exists_normal_lattice_unit_subgroup
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U := by
  classical
  haveI : FiniteDimensional K L := localField_field_module_finite
  obtain ⟨b, n, hb, hu, hl⟩ := localField_exists_integral_normal_lattice K L π hπ
  let A := Submodule.span 𝒪[K] (Set.range b)
  have hA : A.FG := Submodule.fg_span (Set.finite_range b)
  obtain ⟨U, hc, hU⟩ := localField_exists_compact_small_unit_subgroup K L A hA π
    hπ.not_isUnit n hu (fun x hx => hl ⟨x, hx⟩)
  refine ⟨b, n, U, hb, hu, hl, hc, hU, ?_⟩
  intro σ u huU
  apply (hU _).mpr
  have hs := scalarLatticeImage_galois_stable 𝒪[K] K L A
    (fun τ _ hx => normalBasis_span_galois_stable 𝒪[K] K L b hb τ hx)
    (π ^ (n + 1)) σ ((hU u).mp huU)
  simpa only [map_sub, map_one, Units.coe_map] using hs

end
end Dubon2026
