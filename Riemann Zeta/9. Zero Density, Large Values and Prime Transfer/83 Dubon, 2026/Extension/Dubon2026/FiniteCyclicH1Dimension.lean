import Dubon2026.FiniteCyclicCohomologyCardinality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The finite cyclic dimension calculation in the required unramified H1
argument for DUB-17's local deformation dimensions. This uses the pinned
original periodic resolution and genuine homology quotient. The original
continuous local comparison and sufficiently deep unramified stage are
separate arithmetic obligations. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Rank-nullity for the actual homology of a finite-dimensional short
complex, retaining both original differentials. -/
theorem finite_shortComplex_homology_finrank
    {K : Type} [Field K] (S : ShortComplex (ModuleCat K))
    [FiniteDimensional K S.X₁] [FiniteDimensional K S.X₂] :
    Module.finrank K S.homology + Module.finrank K S.f.hom.range +
      Module.finrank K S.g.hom.range = Module.finrank K S.X₂ := by
  have hq := S.moduleCatToCycles.range.finrank_quotient_add_finrank
  have he := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank K S.homology =
    Module.finrank K (S.g.hom.ker ⧸ S.moduleCatToCycles.range) at he
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hfc := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hg := S.g.hom.finrank_range_add_finrank_ker
  have hk : S.moduleCatToCycles.ker = S.f.hom.ker := LinearMap.ker_codRestrict _ _ _
  rw [hk] at hfc
  omega

/-- The original cyclic H1 dimension plus the rank of the actual norm
equals the dimension of the original invariant space. -/
theorem finite_cyclic_H1_finrank_add_norm_range
    {K G : Type} [Field K] [CommGroup G] [Fintype G]
    (A : Rep K G) [FiniteDimensional K A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Module.finrank K (groupCohomology A 1) + Module.finrank K A.ρ.norm.range =
      Module.finrank K A.ρ.invariants := by
  let S := Rep.FiniteCyclicGroup.subCompNormHom A g
  have hdim := finite_shortComplex_homology_finrank S
  have hH := (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide)).toLinearEquiv.finrank_eq
  change Module.finrank K (groupCohomology A 1) = Module.finrank K S.homology at hH
  have hker := (A.ρ g - 1).finrank_range_add_finrank_ker
  have hinv : A.ρ.invariants = LinearMap.ker (A.ρ g - 1) := by
    ext x
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      using Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x
  have hi := (LinearEquiv.ofEq _ _ hinv).finrank_eq
  change Module.finrank K S.homology + Module.finrank K (A.ρ g - 1).range +
    Module.finrank K A.ρ.norm.range = Module.finrank K A at hdim
  omega

/-- Original finite cyclic H1 has dimension at most the invariant space. -/
theorem finite_cyclic_H1_finrank_le_invariants
    {K G : Type} [Field K] [CommGroup G] [Fintype G]
    (A : Rep K G) [FiniteDimensional K A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Module.finrank K (groupCohomology A 1) ≤ Module.finrank K A.ρ.invariants := by
  have h := finite_cyclic_H1_finrank_add_norm_range A g hg
  omega

/-- When the actual finite-stage norm vanishes, the invariant dimension
is attained by the original H1. -/
theorem finite_cyclic_H1_finrank_eq_invariants_of_norm_zero
    {K G : Type} [Field K] [CommGroup G] [Fintype G]
    (A : Rep K G) [FiniteDimensional K A] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (hN : A.ρ.norm = 0) :
    Module.finrank K (groupCohomology A 1) = Module.finrank K A.ρ.invariants := by
  have h := finite_cyclic_H1_finrank_add_norm_range A g hg
  rw [hN, LinearMap.range_zero, finrank_bot, add_zero] at h
  exact h

end
end Dubon2026
