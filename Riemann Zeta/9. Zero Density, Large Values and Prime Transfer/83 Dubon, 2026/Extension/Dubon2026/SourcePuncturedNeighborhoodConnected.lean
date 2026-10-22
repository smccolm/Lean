import Dubon2026.SourceComplexPuncturedBallPaths

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Deleting finitely many points from the
connected original complex curve preserves path connectedness. Punctured
coordinate neighborhoods prevent a separation across a deleted point.
Adapted from S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalExpTopology
noncomputable section
open Filter Topology Set Metric
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem isPreconnected_compl_of_forall_nhd [PreconnectedSpace X] {S : Set X} (hS : IsClosed S)
    (hN : ∀ s ∈ S, ∃ N : Set X, IsOpen N ∧ s ∈ N ∧ N \ {s} ⊆ Sᶜ ∧ IsPreconnected (N \ {s})) :
    IsPreconnected Sᶜ := by
  classical
  choose! N hNo hNs hNsub hNpc using hN
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsuv hdisj

  have hdich : ∀ s ∈ S, N s \ {s} ⊆ u ∨ N s \ {s} ⊆ v := by
    intro s hs
    refine (isPreconnected_iff_subset_of_disjoint.1 (hNpc s hs)) u v hu hv
      ((hNsub s hs).trans hsuv) ?_
    rw [← subset_empty_iff, ← hdisj]
    exact inter_subset_inter_left _ (hNsub s hs)

  have hNS : ∀ s ∈ S, ∀ x ∈ N s, x ∈ S → x = s := by
    intro s hs x hx hxS
    by_contra hne
    exact hNsub s hs ⟨hx, hne⟩ hxS

  set A : Set X := {s | s ∈ S ∧ N s \ {s} ⊆ u} with hA_def
  set B : Set X := {s | s ∈ S ∧ ¬ (N s \ {s} ⊆ u)} with hB_def
  set U : Set X := (u ∩ Sᶜ) ∪ ⋃ s ∈ A, N s with hU_def
  set V : Set X := (v ∩ Sᶜ) ∪ ⋃ s ∈ B, N s with hV_def
  have hBv : ∀ s ∈ B, N s \ {s} ⊆ v := fun s hs => (hdich s hs.1).resolve_left hs.2
  have hUo : IsOpen U :=
    (hu.inter hS.isOpen_compl).union (isOpen_biUnion fun s hs => hNo s hs.1)
  have hVo : IsOpen V :=
    (hv.inter hS.isOpen_compl).union (isOpen_biUnion fun s hs => hNo s hs.1)
  have hcover : univ ⊆ U ∪ V := by
    intro x _
    by_cases hxS : x ∈ S
    · by_cases hxu : N x \ {x} ⊆ u
      · exact Or.inl (Or.inr (mem_biUnion (show x ∈ A from ⟨hxS, hxu⟩) (hNs x hxS)))
      · exact Or.inr (Or.inr (mem_biUnion (show x ∈ B from ⟨hxS, hxu⟩) (hNs x hxS)))
    · rcases hsuv hxS with h | h
      · exact Or.inl (Or.inl ⟨h, hxS⟩)
      · exact Or.inr (Or.inl ⟨h, hxS⟩)
  have hdisj' : univ ∩ (U ∩ V) = ∅ := by
    rw [univ_inter, ← subset_empty_iff]
    rintro x ⟨hxU, hxV⟩
    have hoff : ∀ {x}, x ∈ Sᶜ → x ∈ u → x ∈ v → False := fun hxS hxu hxv => by
      have : _ ∈ Sᶜ ∩ (u ∩ v) := ⟨hxS, hxu, hxv⟩
      rw [hdisj] at this
      exact this

    have hxu : x ∈ Sᶜ → x ∈ u := by
      intro hxS
      rcases hxU with ⟨h, -⟩ | h
      · exact h
      · rw [mem_iUnion₂] at h
        obtain ⟨s, hsA, hxs⟩ := h
        exact hsA.2 ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsA.1)⟩
    have hxv : x ∈ Sᶜ → x ∈ v := by
      intro hxS
      rcases hxV with ⟨h, -⟩ | h
      · exact h
      · rw [mem_iUnion₂] at h
        obtain ⟨s, hsB, hxs⟩ := h
        exact hBv s hsB ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsB.1)⟩
    by_cases hxS : x ∈ S
    ·
      have hxA : x ∈ A := by
        rcases hxU with ⟨-, h⟩ | h
        · exact absurd hxS h
        · rw [mem_iUnion₂] at h
          obtain ⟨s, hsA, hxs⟩ := h
          rw [hNS s hsA.1 x hxs hxS]
          exact hsA
      have hxB : x ∈ B := by
        rcases hxV with ⟨-, h⟩ | h
        · exact absurd hxS h
        · rw [mem_iUnion₂] at h
          obtain ⟨s, hsB, hxs⟩ := h
          rw [hNS s hsB.1 x hxs hxS]
          exact hsB
      exact hxB.2 hxA.2
    · exact hoff hxS (hxu hxS) (hxv hxS)
  rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ) U V hUo hVo hcover hdisj'
    with h | h
  · left
    intro x hxS
    rcases h (mem_univ x) with ⟨hxu, -⟩ | hx
    · exact hxu
    · rw [mem_iUnion₂] at hx
      obtain ⟨s, hsA, hxs⟩ := hx
      exact hsA.2 ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsA.1)⟩
  · right
    intro x hxS
    rcases h (mem_univ x) with ⟨hxv, -⟩ | hx
    · exact hxv
    · rw [mem_iUnion₂] at hx
      obtain ⟨s, hsB, hxs⟩ := hx
      exact hBv s hsB ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsB.1)⟩



end
end Dubon2026.SourceFunctionField.OriginalExpTopology
