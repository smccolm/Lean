import Dubon2026.SourceMeromorphicOrderNeighborhoods

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Analytic transition maps propagate zero germs
and isolated nonzero orders. Connectedness separates the identically zero
case; compactness makes the pole set finite. These results supply an actual
effective divisor for the proved original Riemann-Roch inequality.
Adapted from S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

variable [ConnectedSpace (M)]

theorem forall_order_eq_top_or (ψ : M → ℂ) (hψ : ∀ v, MeromorphicAt (rd ψ v) (ctr v)) :
    (∀ v, meromorphicOrderAt (rd ψ v) (ctr v) = ⊤) ∨ ∀ v, meromorphicOrderAt (rd ψ v) (ctr v) ≠ ⊤ := by
  set A : Set (M) := {v | meromorphicOrderAt (rd ψ v) (ctr v) = ⊤} with hA
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    exact eventually_order_eq_top ψ (meromorphicOrderAt_eq_top_iff.1 hv)
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro v hv
    have hne : ∀ᶠ z in (𝓝[≠] (ctr v)), rd ψ v z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hψ v)).1 hv
    filter_upwards [eventually_order_eq_zero ψ (hψ v) hne] with w hw
    by_cases hwv : w = v
    · rw [hwv]; exact hv
    · intro hwA
      have := (hw hwv).2
      rw [show meromorphicOrderAt (rd ψ w) (ctr w) = ⊤ from hwA] at this
      exact WithTop.top_ne_zero this
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
  · right
    intro v hv
    have : v ∈ A := hv
    rw [h] at this
    exact this
  · left
    intro v
    have : v ∈ A := by rw [h]; exact mem_univ v
    exact this

variable [CompactSpace (M)]

omit [ConnectedSpace (M)] in

theorem finite_setOf_order_neg (ψ : M → ℂ) (hψ : ∀ v, MeromorphicAt (rd ψ v) (ctr v))
    (hfin : ∀ v, meromorphicOrderAt (rd ψ v) (ctr v) ≠ ⊤) :
    {v | meromorphicOrderAt (rd ψ v) (ctr v) < 0}.Finite := by

  have hU : ∀ v : M, ∃ U ∈ 𝓝 v, ∀ w ∈ U, w ≠ v → meromorphicOrderAt (rd ψ w) (ctr w) = 0 := by
    intro v
    have hne : ∀ᶠ z in (𝓝[≠] (ctr v)), rd ψ v z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hψ v)).1 (hfin v)
    exact ⟨_, eventually_order_eq_zero ψ (hψ v) hne, fun w hw hwv => (hw hwv).2⟩
  choose U hUn hUz using hU
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover U fun v _ => hUn v
  refine (t.finite_toSet).subset fun w hw => ?_
  obtain ⟨v, hv, hwU⟩ := mem_iUnion₂.1 (hcover (mem_univ w))
  by_contra hwt
  have hne : w ≠ v := fun h => hwt (h ▸ hv)
  have h0 := hUz v w hwU hne
  have hlt : meromorphicOrderAt (rd ψ w) (ctr w) < 0 := hw
  rw [h0] at hlt
  exact lt_irrefl _ hlt


end
end Dubon2026.SourceFunctionField.MeromorphicCompact
