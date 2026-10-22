import Dubon2026.SourceOriginalJCovering

/-! DUB-17/18 -> geometric cell dissection -> original sheet coordinates.
Lift sheets from the actual open regular locus to original places, retaining
targets, exact evaluation, disjointness and exhaustion. This is a conditional
conversion; the actual j-covering supplies the sheets in the next consumer.
Adapted from S_AlgebraicCurve_exists_dissectionScaleData,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Actual disjoint sheets of original evaluation, with their complete fiber exhaustion. -/
def IsOriginalSheetFamily {ι : Type*} (x : F) (V : Set ℂ) (ζ : ι → OpenPartialHomeomorph (Place ℂ F) ℂ) :
    Prop :=
  (∀ i, (ζ i).target = V) ∧
  (∀ i, ∀ P ∈ (ζ i).source, x ∈ P.toValuationSubring ∧ ζ i P = originalPlaceEval N ℂ P x) ∧
  (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
  (∀ P : Place ℂ F, x ∈ P.toValuationSubring → originalPlaceEval N ℂ P x ∈ V → ∃ i, P ∈ (ζ i).source)

theorem IsOriginalSheetFamily.reindex {ι κ : Type*} {x : F} {V : Set ℂ}
    {ζ : ι → OpenPartialHomeomorph (Place ℂ F) ℂ} (h : IsOriginalSheetFamily x V ζ) (e : κ ≃ ι) :
    IsOriginalSheetFamily x V (fun k => ζ (e k)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k => h1 (e k), fun k => h2 (e k), ?_, ?_⟩
  · intro k k' hkk'
    exact h3 (fun hek => hkk' (e.injective hek))
  · intro P hP hPV
    obtain ⟨i, hi⟩ := h4 P hP hPV
    refine ⟨e.symm i, ?_⟩
    show P ∈ (ζ (e (e.symm i))).source
    rw [e.apply_symm_apply]
    exact hi


theorem exists_original_sheet_family_of_subtype {x : F}
    [Nonempty {P : Place ℂ F // x ∈ P.toValuationSubring}] {ι : Type*} {V : Set ℂ}
    (ζ' : ι → OpenPartialHomeomorph {P : Place ℂ F // x ∈ P.toValuationSubring} ℂ)
    (htarget : ∀ i, (ζ' i).target = V)
    (hfwd : ∀ i, ∀ e ∈ (ζ' i).source, ζ' i e = originalPlaceEval N ℂ e.1 x)
    (hdisj : Pairwise fun i j => Disjoint (ζ' i).source (ζ' j).source)
    (hexh : ∀ e : {P : Place ℂ F // x ∈ P.toValuationSubring},
      originalPlaceEval N ℂ e.1 x ∈ V → ∃ i, e ∈ (ζ' i).source) :
    ∃ ζ : ι → OpenPartialHomeomorph (Place ℂ F) ℂ, IsOriginalSheetFamily x V ζ := by
  have hopen := OriginalChart.isOpen_original_regular_locus N x
  have hemb : Topology.IsOpenEmbedding
      (Subtype.val : {P : Place ℂ F // x ∈ P.toValuationSubring} → Place ℂ F) :=
    hopen.isOpenEmbedding_subtypeVal
  have hinv : ∀ e : {P : Place ℂ F // x ∈ P.toValuationSubring},
      (hemb.toOpenPartialHomeomorph Subtype.val).symm (e : Place ℂ F) = e :=
    fun _ => hemb.toOpenPartialHomeomorph_left_inv
  have hsrc : ∀ (i : ι) (P : Place ℂ F),
      P ∈ ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)).source ↔
        ∃ e : {P : Place ℂ F // x ∈ P.toValuationSubring}, (e : Place ℂ F) = P ∧ e ∈ (ζ' i).source := by
    intro i P
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    constructor
    · rintro ⟨⟨e, rfl⟩, he⟩
      rw [Set.mem_preimage, hinv e] at he
      exact ⟨e, rfl, he⟩
    · rintro ⟨e, rfl, he⟩
      refine ⟨⟨e, rfl⟩, ?_⟩
      rw [Set.mem_preimage, hinv e]
      exact he
  have h1 : ∀ i, ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)).target = V := by
    intro i
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ,
      htarget i]
  have h2 : ∀ i, ∀ P ∈ ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)).source,
      x ∈ P.toValuationSubring ∧
        ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)) P = originalPlaceEval N ℂ P x := by
    intro i P hP
    obtain ⟨e, rfl, he⟩ := (hsrc i P).mp hP
    refine ⟨e.2, ?_⟩
    rw [OpenPartialHomeomorph.trans_apply, hinv e]
    exact hfwd i e he
  have h3 : Pairwise fun i j => Disjoint
      ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)).source
      ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' j)).source := by
    intro i j hij
    rw [Set.disjoint_left]
    intro P hPi hPj
    obtain ⟨e, rfl, hei⟩ := (hsrc i P).mp hPi
    obtain ⟨e', he', hej⟩ := (hsrc j _).mp hPj
    rw [Subtype.ext he'] at hej
    exact Set.disjoint_left.mp (hdisj hij) hei hej
  have h4 : ∀ P : Place ℂ F, x ∈ P.toValuationSubring → originalPlaceEval N ℂ P x ∈ V →
      ∃ i, P ∈ ((hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i)).source := by
    intro P hPx hPV
    obtain ⟨i, hi⟩ := hexh ⟨P, hPx⟩ hPV
    exact ⟨i, (hsrc i P).mpr ⟨⟨P, hPx⟩, rfl, hi⟩⟩
  exact ⟨fun i => (hemb.toOpenPartialHomeomorph Subtype.val).symm.trans (ζ' i), h1, h2, h3, h4⟩


end
end Dubon2026.SourceFunctionField.CellGeometry
