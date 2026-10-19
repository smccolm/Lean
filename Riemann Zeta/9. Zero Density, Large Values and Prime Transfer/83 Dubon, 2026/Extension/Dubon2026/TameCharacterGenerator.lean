/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ExtCitation_exists_tame_generator_at_level.lean, quotient_form.
Modified to isolate the character-generation argument, use native subgroup APIs and
default proof limits. This constructs the finite tame generator required by the
ramified auxiliary deformation condition -> arithmetic patching -> Dubon Theorem 2.6.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace Dubon2026

theorem subgroup_eq_character_kernel_sup_zpowers
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) (θ : I →* H)
    [IsCyclic θ.range] :
    ∃ t ∈ I, I = θ.ker.map I.subtype ⊔ Subgroup.zpowers t := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := θ.range)
  obtain ⟨t, ht⟩ := g₀.property
  refine ⟨t, t.property, le_antisymm ?_ ?_⟩
  · intro s hs
    have hmem : (⟨θ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩⟩ : θ.range) ∈ Subgroup.zpowers g₀ := hg₀ _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : θ t ^ k = θ ⟨s, hs⟩ := by
      have h := congrArg (fun z : θ.range => (z : H)) hk
      simpa only [SubgroupClass.coe_zpow, ht] using h
    have hu : s * (t : G) ^ (-k) ∈ θ.ker.map I.subtype := by
      refine ⟨⟨s, hs⟩ * t ^ (-k), ?_, rfl⟩
      change θ (⟨s, hs⟩ * t ^ (-k)) = 1
      rw [map_mul, map_zpow, ← hk', ← zpow_add, add_neg_cancel, zpow_zero]
    have he : s = (s * (t : G) ^ (-k)) * (t : G) ^ k := by
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [he]
    exact Subgroup.mul_mem_sup hu (Subgroup.zpow_mem_zpowers _ _)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · rw [Subgroup.zpowers_le]
      exact t.property

end Dubon2026
