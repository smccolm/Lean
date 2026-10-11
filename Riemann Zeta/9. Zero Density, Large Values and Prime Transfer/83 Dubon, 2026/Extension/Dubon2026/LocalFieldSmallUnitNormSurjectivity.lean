import Dubon2026.LocalFieldNormalUnitLevelNorm
import Dubon2026.LocalFieldAlgEquivContinuity
import Dubon2026.LocalFieldOpenSmallUnits
import Dubon2026.CompactFilteredUnitNorm

/-! # Exact original norm preimages in genuine compact open normal-lattice units -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Construct actual compact open Galois-stable normal-lattice units with
finite original integer-unit quotient and exact norm preimages for all their
invariants. Every-level corrections, separation and continuity are derived
from the same original field and normal basis before compactness is applied. -/
theorem localField_exists_small_unit_norm_surjective
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
      ∃ F : ℕ → Subgroup Lˣ, F 0 = U ∧
        (∀ j, IsCompact (F j : Set Lˣ) ∧
          (∀ u : Lˣ, u ∈ F j ↔ (u : L) - 1 ∈
            scalarLatticeImage
              (scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)))
              (π ^ j)) ∧
          (∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ F j →
            Units.map (σ : L →+* L).toMonoidHom u ∈ F j) ∧
          F (j + 1) ≤ F j) ∧
        ∀ u : Lˣ, (∀ j, u ∈ F j) → u = 1 := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : FiniteDimensional K L := localField_field_module_finite
  obtain ⟨b, n, F, hb, hupper, hlower, hF, hsep⟩ :=
    localField_exists_separated_normal_unit_filtration K L π hπ
  have hzero : ∀ u : Lˣ, u ∈ F 0 ↔ (u : L) - 1 ∈
      scalarLatticeImage (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)) := by
    intro u
    simpa only [pow_zero, mem_scalarLatticeImage, one_smul, exists_eq_right] using (hF 0).2.1 u
  have hopen := localField_small_unit_subgroup_isOpen K L _ π hπ.ne_zero n hlower (F 0) hzero
  refine ⟨b, n, F 0, hb, hupper, hlower, (hF 0).1, hopen,
    localField_integer_unit_quotient_finite L (F 0) hopen, hzero, (hF 0).2.2.1,
    ?_, F, rfl, hF, hsep⟩
  intro u hu hinv
  apply finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration Gal(L/K) Lˣ F
    (fun j => (hF j).2.2.2) (hF 0).1 (fun j => (hF j).1.isClosed) hsep
    (fun σ => localField_algEquiv_units_continuous K L L σ) ?_ u hu hinv
  intro j v hv hi
  exact localField_normal_unit_level_norm_correction K L b hb π hπ n hupper hlower F
    (fun j => (hF j).2.1) (fun j => (hF j).2.2.1) j v hv hi

end
end Dubon2026
