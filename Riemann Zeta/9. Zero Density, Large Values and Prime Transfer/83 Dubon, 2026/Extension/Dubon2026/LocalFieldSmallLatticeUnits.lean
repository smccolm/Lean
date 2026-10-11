import Dubon2026.ScaledLatticeProducts
import Dubon2026.LocalFieldCompactLattice
import Dubon2026.CompactLatticeUnitSubgroup

/-! # Actual compact small-unit groups in original local fields -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Every original element of the scaled integral lattice lies above the
original maximal ideal of the extension integer ring. Consequently its sum
with one is nonzero in the original extension field. -/
theorem localField_scaled_lattice_one_add_ne_zero
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : ¬ IsUnit π) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    {x : L} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1))) :
    (1 : L) + x ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A _ x).mp hx
  let aI : 𝒪[L] := ⟨a, hupper a ha⟩
  let z : 𝒪[L] := (algebraMap 𝒪[K] 𝒪[L] π) ^ (n + 1) * aI
  have hπm : algebraMap 𝒪[K] 𝒪[L] π ∈ IsLocalRing.maximalIdeal 𝒪[L] :=
    map_nonunit (algebraMap 𝒪[K] 𝒪[L]) π (by simpa using hπ)
  have hzm : z ∈ IsLocalRing.maximalIdeal 𝒪[L] :=
    (IsLocalRing.maximalIdeal 𝒪[L]).mul_mem_right aI
      ((IsLocalRing.maximalIdeal 𝒪[L]).pow_mem_of_mem hπm (n + 1) (Nat.succ_pos n))
  have hz : (z : L) = π ^ (n + 1) • a := by
    change ((algebraMap 𝒪[K] 𝒪[L] π : 𝒪[L]) : L) ^ (n + 1) * a = _
    rw [Algebra.smul_def]
    change algebraMap 𝒪[L] L
        ((algebraMap 𝒪[K] 𝒪[L] π) ^ (n + 1) * aI) =
      algebraMap 𝒪[K] L (π ^ (n + 1)) * a
    simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    rfl
  intro hzero
  have hz0 : (1 : 𝒪[L]) + z = 0 := by
    apply Subtype.ext
    change (1 : L) + (z : L) = 0
    rwa [hz]
  have hone : (1 : 𝒪[L]) ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [eq_neg_of_add_eq_zero_left hz0]
    exact (IsLocalRing.maximalIdeal 𝒪[L]).neg_mem hzm
  exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone

/-- The actual scaled lattice supplies a compact subgroup of original field
units, with its carrier exactly the units whose difference from one lies in
that same lattice. Compactness, multiplication and inverse closure are derived
from the actual finite lattice and its two original integral bounds. -/
theorem localField_exists_compact_small_unit_subgroup
    (A : Submodule 𝒪[K] L) (hA : A.FG)
    (π : 𝒪[K]) (hπ : ¬ IsUnit π) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ (ValuativeRel.valuation L).integer)
    (hlower : ∀ x ∈ (ValuativeRel.valuation L).integer, π ^ n • x ∈ A) :
    ∃ U : Subgroup Lˣ, IsCompact (U : Set Lˣ) ∧
      ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ scalarLatticeImage A (π ^ (n + 1)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  let Λ := scalarLatticeImage A (π ^ (n + 1))
  have hΛ : Λ.FG := hA.map _
  have hc : IsCompact (Λ : Set L) := localField_finite_lattice_isCompact K L Λ hΛ
  have hm : ∀ x ∈ Λ.toAddSubgroup, ∀ y ∈ Λ.toAddSubgroup, x * y ∈ Λ.toAddSubgroup := by
    intro x hx y hy
    exact scalarLatticeImage_mul_mem A (ValuativeRel.valuation L).integer π n
      hupper hlower hx hy
  have hn : ∀ x ∈ Λ.toAddSubgroup, (1 : L) + x ≠ 0 := by
    intro x hx
    exact localField_scaled_lattice_one_add_ne_zero K L A π hπ n hupper hx
  let M := latticeUnitSubmonoid Λ.toAddSubgroup hm
  have hM : IsCompact (M : Set Lˣ) :=
    latticeUnitSubmonoid_isCompact Λ.toAddSubgroup hm hc hn
  exact ⟨compactSubmonoidSubgroup M hM, hM, fun _ => Iff.rfl⟩

end
end Dubon2026
