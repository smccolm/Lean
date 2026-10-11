import Dubon2026.LocalFieldIntegralNormalLattice
import Dubon2026.NormalBasisLatticeCohomology
import Dubon2026.FiniteBasisAdicCompleteness

/-! # Actual complete normal lattices and their original additive cohomology -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel BigOperators

/-- Construct one actual integral normal lattice in the original local
Galois field, together with its original ideal-power bounds, actual adic
completeness, positive additive cohomology vanishing and explicit norm
surjectivity onto its original invariants. Multiplicative units are a separate step. -/
theorem localField_exists_complete_normal_lattice
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    ∃ (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (n : ℕ),
      (∀ x ∈ Submodule.span 𝒪[K] (Set.range b),
        x ∈ (ValuativeRel.valuation L).integer) ∧
      (∀ x : 𝒪[L], π ^ n • (x : L) ∈ Submodule.span 𝒪[K] (Set.range b)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K])
        (Submodule.span 𝒪[K] (Set.range b)) ∧
      (∀ m : ℕ, CategoryTheory.Limits.IsZero
        (groupCohomology (normalBasisLatticeRep 𝒪[K] K L b hb) (m + 1))) ∧
      ∀ a : Submodule.span 𝒪[K] (Set.range b),
        (∀ σ, (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ a = a) →
        ∃ x : Submodule.span 𝒪[K] (Set.range b),
          ∑ σ : Gal(L/K), (normalBasisLatticeRep 𝒪[K] K L b hb).ρ σ x = a := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : FiniteDimensional K L := localField_field_module_finite
  obtain ⟨b, n, hb, hint, hbound⟩ := localField_exists_integral_normal_lattice K L π hπ
  refine ⟨b, hb, n, hint, hbound, ?_, ?_, ?_⟩
  · exact finiteBasis_isAdicComplete (b.restrictScalars 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[K])
  · exact normalBasisLattice_groupCohomology_isZero 𝒪[K] K L b hb
  · exact normalBasisLattice_invariant_mem_norm 𝒪[K] K L b hb

end
end Dubon2026
