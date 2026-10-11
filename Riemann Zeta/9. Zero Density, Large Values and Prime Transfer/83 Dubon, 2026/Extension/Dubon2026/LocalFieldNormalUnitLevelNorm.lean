import Dubon2026.NormalLatticeUnitCorrection
import Dubon2026.LocalFieldSeparatedNormalUnitFiltration
import Dubon2026.FiniteActionUnitNorm

/-! # Actual norm corrections at every original local normal-lattice level -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel BigOperators

/-- The original normal basis and its actual integer bounds derive a genuine
norm correction at every level of the same scalar unit filtration. Neither
quotient cohomology nor one-step norm surjectivity is assumed. -/
theorem localField_normal_unit_level_norm_correction
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ)
    (hupper : ∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
      x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b))
    (U : ℕ → Subgroup Lˣ)
    (hU : ∀ j (u : Lˣ), u ∈ U j ↔ (u : L) - 1 ∈
      scalarLatticeImage
        (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1))) (π ^ j))
    (hstable : ∀ j (σ : Gal(L/K)) (u : Lˣ), u ∈ U j →
      Units.map (σ : L →+* L).toMonoidHom u ∈ U j)
    (j : ℕ) (u : Lˣ) (hu : u ∈ U j) (hinv : ∀ σ : Gal(L/K), σ • u = u) :
    ∃ v : Lˣ, v ∈ U j ∧ u / finiteActionUnitNorm Gal(L/K) Lˣ v ∈ U (j + 1) := by
  classical
  let A := Submodule.span 𝒪[K] (Set.range b)
  let B := scalarLatticeImage A (π ^ (n + 1))
  let r := π ^ j * π ^ (n + 1)
  have hr : r ≠ 0 := mul_ne_zero (pow_ne_zero j hπ.ne_zero) (pow_ne_zero _ hπ.ne_zero)
  have hid : scalarLatticeImage B (π ^ j) = scalarLatticeImage A r :=
    scalarLatticeImage_scalar_image A (π ^ (n + 1)) (π ^ j)
  have hgain : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ scalarLatticeImage B π := by
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := scalarLatticeImage_product_gain A
      (ValuativeRel.valuation L).integer π n hupper (fun a ha => hlower ⟨a, ha⟩) hx hy
    exact (mem_scalarLatticeImage B π (x * y)).mpr ⟨z, hz, he.symm⟩
  have hUr : ∀ v : Lˣ, v ∈ U j ↔ (v : L) - 1 ∈ scalarLatticeImage A r := by
    intro v
    rw [hU j, hid]
  have hmul : ∀ x ∈ scalarLatticeImage A r, ∀ y ∈ scalarLatticeImage A r,
      x * y ∈ scalarLatticeImage (scalarLatticeImage A r) π := by
    intro x hx y hy
    rw [← hid] at hx hy ⊢
    exact scalarLatticeImage_level_product_gain B π hgain j hx hy
  have hunit : ∀ x ∈ scalarLatticeImage A r, (1 : L) + x ≠ 0 := by
    intro x hx
    rw [← hid] at hx
    exact localField_scaled_lattice_one_add_ne_zero K L A π hπ.not_isUnit n hupper
      (scalarLatticeImage_le B (π ^ j) hx)
  let uj : U j := ⟨u, hu⟩
  have hui : ∀ σ : Gal(L/K), galoisUnitSubgroupMap K L (U j) (hstable j) σ uj = uj := by
    intro σ
    exact Subtype.ext (hinv σ)
  obtain ⟨v, hv⟩ := normalLatticeUnit_norm_correction 𝒪[K] K L b hb r π hr hπ.ne_zero
    (U j) (hstable j) hUr hmul hunit uj hui
  have hn : ((∏ σ : Gal(L/K), galoisUnitSubgroupMap K L (U j) (hstable j) σ v : U j) : Lˣ) =
      finiteActionUnitNorm Gal(L/K) Lˣ (v : Lˣ) := by
    change (U j).subtype (∏ σ : Gal(L/K), galoisUnitSubgroupMap K L (U j) (hstable j) σ v) = _
    rw [map_prod]
    rfl
  change (((u / ((∏ σ : Gal(L/K), galoisUnitSubgroupMap K L (U j) (hstable j) σ v : U j) : Lˣ)) : Lˣ) : L) - 1 ∈
    scalarLatticeImage (scalarLatticeImage A r) π at hv
  rw [hn] at hv
  refine ⟨v, v.property, (hU (j + 1) _).mpr ?_⟩
  rw [scalarLatticeImage_pow_succ]
  change _ ∈ scalarLatticeImage (scalarLatticeImage B (π ^ j)) π
  rwa [hid]

end
end Dubon2026
