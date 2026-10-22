import Dubon2026.SourceOriginalPairedArcOverlap

/-! DUB-17/18 -> original Abel-Jacobi -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellDissection OriginalChart
open scoped Topology Manifold
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem arc_subset_of_arc_rev (𝒟 : CellDissection N) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (C' : 𝒟.ιC) (k' : Fin (𝒟.cell C').R.N) (he : (𝒟.side C k).1 = (𝒟.side C' k').1)
    (h1 : (𝒟.side C k).2 = true) (h2 : (𝒟.side C' k').2 = false) :
    (𝒟.cell C').arc k' = (𝒟.cell C).arc k := by
  obtain ⟨ψ, hanti, hC1, hψa, hψb, hbd⟩ := 𝒟.arc_rev C k C' k' he h1 h2
  have hab := (𝒟.cell C).R.hmono (Fin.castSucc_lt_succ (i := k))
  have hab' := (𝒟.cell C').R.hmono (Fin.castSucc_lt_succ (i := k'))
  have hcont : ContinuousOn ψ ((𝒟.cell C').R.arcIcc k') := hC1.continuousOn

  have hmaps : ∀ t ∈ (𝒟.cell C').R.arcIcc k', ψ t ∈ (𝒟.cell C).R.arcIcc k := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [← hψb]; exact hanti.antitoneOn ht (right_mem_Icc.2 hab'.le) ht.2
    · rw [← hψa]; exact hanti.antitoneOn (left_mem_Icc.2 hab'.le) ht ht.1
  have hsurj : ∀ s ∈ (𝒟.cell C).R.arcIcc k, ∃ t ∈ (𝒟.cell C').R.arcIcc k', ψ t = s := by
    intro s hs
    have := intermediate_value_Icc' hab'.le hcont
    rw [hψa, hψb] at this
    exact this hs
  apply Subset.antisymm
  · rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨(𝒟.cell C).R.loop (ψ t), ⟨ψ t, hmaps t ht, rfl⟩, ?_⟩
    exact (hbd t ht).symm
  · rintro x ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hsurj s hs
    exact ⟨(𝒟.cell C').R.loop t, ⟨t, ht, rfl⟩, hbd t ht⟩

theorem arc_eq_of_side (𝒟 : CellDissection N) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (C' : 𝒟.ιC) (k' : Fin (𝒟.cell C').R.N) (he : (𝒟.side C k).1 = (𝒟.side C' k').1) :
    (𝒟.cell C).arc k = (𝒟.cell C').arc k' := by
  by_cases hs : (𝒟.side C k).2 = (𝒟.side C' k').2
  ·
    have heq : 𝒟.side C k = 𝒟.side C' k' := Prod.ext he hs
    have := 𝒟.side_bij.injective (a₁ := ⟨C, k⟩) (a₂ := ⟨C', k'⟩) heq
    cases this
    rfl
  · cases h : (𝒟.side C k).2
    · have h' : (𝒟.side C' k').2 = true := by
        cases h'' : (𝒟.side C' k').2
        · exact absurd (h.trans h''.symm) hs
        · rfl
      exact arc_subset_of_arc_rev 𝒟 C' k' C k he.symm h' h
    · have h' : (𝒟.side C' k').2 = false := by
        cases h'' : (𝒟.side C' k').2
        · rfl
        · exact absurd (h.trans h''.symm) hs
      exact (arc_subset_of_arc_rev 𝒟 C k C' k' he h h').symm
end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
