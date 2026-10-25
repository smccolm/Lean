import Dubon2026.SourceRadialPairedArcOverlap

/-! DUB-17/18 -> cover Abel converse -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
open Set Filter RadialCellDissection
open scoped Topology
variable {X : Type*} [TopologicalSpace X] {κ : Type*}

theorem arc_subset_of_arc_rev (𝒟 : RadialCellDissection X) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (C' : 𝒟.ιC) (k' : Fin (𝒟.cell C').R.N) (he : (𝒟.side C k).1 = (𝒟.side C' k').1)
    (h1 : (𝒟.side C k).2 = true) (h2 : (𝒟.side C' k').2 = false) :
    (𝒟.cell C').arc k' = (𝒟.cell C).arc k := by
  obtain ⟨ψ, hanti, hC1, hψa, hψb, hbd⟩ := 𝒟.arc_rev C k C' k' he h1 h2
  exact RadialRegion.reversed_arc_images (𝒟.cell C).R (𝒟.cell C').R k k'
    (𝒟.cell C).ζ.symm (𝒟.cell C').ζ.symm ψ hanti hC1.continuousOn hψa hψb hbd

theorem arc_eq_of_side (𝒟 : RadialCellDissection X) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
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
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
