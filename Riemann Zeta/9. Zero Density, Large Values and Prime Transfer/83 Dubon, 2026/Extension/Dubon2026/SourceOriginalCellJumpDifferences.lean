import Dubon2026.SourceOriginalPairedArcEquality
import Dubon2026.SourceOriginalPolygonPrimitiveData
import Dubon2026.SourceOriginalPairedBoundarySum

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

/-- Cells joined by a common actual geometric edge through the specified point. -/
def LinkedAt (D : CellDissection N) (x : Place ℂ F) (A B : D.ιC) : Prop :=
  ∃ (k : Fin (D.cell A).R.N) (k' : Fin (D.cell B).R.N),
    (D.side A k).1 = (D.side B k').1 ∧ x ∈ (D.cell A).arc k

variable {𝒟 : CellDissection N} {Ψ : κ → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → κ → ℂ}

theorem gvec_sub_mem_of_linkedAt (hJ : IsJump 𝒟 Ψ J) {x : Place ℂ F} {D E : 𝒟.ιC}
    (h : LinkedAt 𝒟 x D E) :
    gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E ∈ AddSubgroup.closure (Set.range J) := by
  obtain ⟨k, k', he, hx⟩ := h
  set e := (𝒟.side D k).1 with hedef
  by_cases hs : (𝒟.side D k).2 = (𝒟.side E k').2
  · have heq : 𝒟.side D k = 𝒟.side E k' := Prod.ext he hs
    have := 𝒟.side_bij.injective (a₁ := ⟨D, k⟩) (a₂ := ⟨E, k'⟩) heq
    cases this
    rw [sub_self]
    exact zero_mem _

  have hDk : ∀ (σ : Bool), (𝒟.side D k).2 = σ → arcOf 𝒟 (e, σ) = ⟨D, k⟩ := by
    intro σ hσ
    have : 𝒟.side D k = (e, σ) := Prod.ext rfl hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨D, k⟩
  have hEk : ∀ (σ : Bool), (𝒟.side E k').2 = σ → arcOf 𝒟 (e, σ) = ⟨E, k'⟩ := by
    intro σ hσ
    have : 𝒟.side E k' = (e, σ) := Prod.ext he.symm hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨E, k'⟩

  have hjump : gvec 𝒟 Ψ x (arcOf 𝒟 (e, true)).1 - gvec 𝒟 Ψ x (arcOf 𝒟 (e, false)).1 = J e := by

    have hx' : x ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).arc (arcOf 𝒟 (e, true)).2 := by
      have hside : (𝒟.side D k).1 = (𝒟.side (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).1 := by
        rw [side_arcOf]
      rwa [arc_eq_of_side 𝒟 D k _ _ hside] at hx
    obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hx'
    funext i
    have h := hJ i e s hs
    simp only [gvec, Pi.sub_apply]
    have ht : (𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).ζ.target :=
      (𝒟.cell _).hKt (RadialRegion.loop_mem_K _ s)
    rw [(𝒟.cell (arcOf 𝒟 (e, true)).1).ζ.right_inv ht]
    exact h
  cases hD2 : (𝒟.side D k).2
  · have hE2 : (𝒟.side E k').2 = true := by
      cases h' : (𝒟.side E k').2
      · exact absurd (hD2.trans h'.symm) hs
      · rfl
    have h1 := hDk false hD2
    have h2 := hEk true hE2
    rw [h1, h2] at hjump

    have : gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E = -J e := by rw [← hjump]; abel
    rw [this]
    exact AddSubgroup.neg_mem _ (AddSubgroup.subset_closure ⟨e, rfl⟩)
  · have hE2 : (𝒟.side E k').2 = false := by
      cases h' : (𝒟.side E k').2
      · rfl
      · exact absurd (hD2.trans h'.symm) hs
    have h1 := hDk true hD2
    have h2 := hEk false hE2
    rw [h1, h2] at hjump
    rw [hjump]
    exact AddSubgroup.subset_closure ⟨e, rfl⟩

theorem gvec_sub_mem (hJ : IsJump 𝒟 Ψ J) {x : Place ℂ F} {D E : 𝒟.ιC}
    (hD : x ∈ (𝒟.cell D).carrier) (hE : x ∈ (𝒟.cell E).carrier) :
    gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E ∈ AddSubgroup.closure (Set.range J) := by
  have hlink := 𝒟.inter D E x hD hE
  clear hD hE
  induction hlink with
  | refl => rw [sub_self]; exact zero_mem _
  | tail _ hbc ih =>
    have := add_mem ih (gvec_sub_mem_of_linkedAt hJ hbc)
    rwa [sub_add_sub_cancel] at this
end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
