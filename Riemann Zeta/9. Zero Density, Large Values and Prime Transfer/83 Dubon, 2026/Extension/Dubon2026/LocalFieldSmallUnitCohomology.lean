import Dubon2026.LocalFieldSmallUnitNormSurjectivity
import Dubon2026.LocalFieldNormalUnitLevelCocycle
import Dubon2026.CompactFilteredUnitCocycles

/-! # Original norms and coboundaries in the same actual small-unit subgroup -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- One genuine compact open Galois-stable subgroup of original local-field
units has both exact invariant norm preimages and original unit preimages
for every original multiplicative one-cocycle. The same constructed normal
basis and separating filtration supply both results. -/
theorem localField_exists_small_unit_norm_and_coboundary
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (n : ℕ) (U : Subgroup Lˣ),
      (∀ σ, b σ = σ (b 1)) ∧
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsCompact (U : Set Lˣ) ∧ IsOpen (U : Set Lˣ) ∧
      Finite (𝒪[L]ˣ ⧸ U.comap (Units.map (algebraMap 𝒪[L] L).toMonoidHom)) ∧
      (∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
        scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) ∧
      (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
        Units.map (σ : L →+* L).toMonoidHom u ∈ U) ∧
      (∀ u : Lˣ, u ∈ U → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : Lˣ, v ∈ U ∧ finiteActionUnitNorm Gal(L/K) Lˣ v = u) ∧
      ∀ c : Gal(L/K) → Lˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ U) →
          ∃ v : Lˣ, v ∈ U ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : FiniteDimensional K L := localField_field_module_finite
  obtain ⟨b, n, U, hb, hupper, hlower, hcompact, hopen, hfinite, hU, hstable,
    hnorm, F, hFU, hF, hsep⟩ := localField_exists_small_unit_norm_surjective K L π hπ
  refine ⟨b, n, U, hb, hupper, hlower, hcompact, hopen, hfinite, hU, hstable, hnorm, ?_⟩
  intro c hc hcU
  have hc0 : ∀ σ, c σ ∈ F 0 := by
    intro σ
    simpa only [hFU] using hcU σ
  have hcorrect : ∀ j (a : Gal(L/K) → Lˣ),
      (∀ σ τ, a (σ * τ) = (σ • a τ) * a σ) → (∀ σ, a σ ∈ F j) →
        ∃ v : Lˣ, v ∈ F j ∧ ∀ σ : Gal(L/K), a σ / ((σ • v) / v) ∈ F (j + 1) := by
    intro j a ha haj
    exact localField_normal_unit_level_cocycle_correction K L b hb π hπ n hupper hlower F
      (fun j => (hF j).2.1) (fun j => (hF j).2.2.1) j a ha haj
  obtain ⟨v, hv, he⟩ := unit_cocycle_coboundary_of_compact_filtration F
    (fun j => (hF j).2.2.2) (hF 0).1 (fun j => (hF j).1.isClosed) hsep
    (fun σ => localField_algEquiv_units_continuous K L L σ) hcorrect c hc hc0
  exact ⟨v, hFU ▸ hv, he⟩

end
end Dubon2026
