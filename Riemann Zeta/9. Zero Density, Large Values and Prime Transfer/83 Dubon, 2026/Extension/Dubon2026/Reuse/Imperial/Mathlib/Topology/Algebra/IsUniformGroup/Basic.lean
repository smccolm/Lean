/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

/- Adaptation for Dubon at its unchanged Lean/Mathlib pin. Original Apache-2.0
source: https://github.com/ImperialCollegeLondon/FLT/blob/1ab58c167e4fc60bef518cc02caa3fc15c9590d5/FLT/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean
The original copyright and license are retained in Dependencies/ImperialPatchingReuse/LICENSE.
Arithmetic patching-system realization is not supplied by these generic proofs. -/

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Dubon2026.Reuse.Imperial.Mathlib.GroupTheory.Index

/-!
# Total boundedness for topological groups with small finite-index subgroups

Material destined for Mathlib.
-/

@[expose] public section

lemma IsTopologicalGroup.totallyBounded {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ∀ s ∈ nhds (1 : G), ∃ H : Subgroup G, H.FiniteIndex ∧ ↑H ⊆ s) :
    letI := IsTopologicalGroup.rightUniformSpace G
    TotallyBounded (Set.univ : Set G) := by
  let := IsTopologicalGroup.rightUniformSpace G
  rintro s ⟨t, ht1, hts⟩
  obtain ⟨H, hH, hHs⟩ := H _ ht1
  have : Finite (Gᵐᵒᵖ ⧸ H.op) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (MulOpposite.unop ∘ Quotient.out : Gᵐᵒᵖ ⧸ H.op → G),
    Set.finite_range _, fun x _ ↦
      Set.mem_iUnion₂_of_mem ⟨QuotientGroup.mk (.op x), rfl⟩ (hts (hHs ?_))⟩
  dsimp only
  rw [Function.comp_apply, SetLike.mem_coe, ← MulOpposite.unop_op (x⁻¹),
    ← MulOpposite.unop_mul, ← Subgroup.mem_op, MulOpposite.op_inv, ← QuotientGroup.eq]
  simp
