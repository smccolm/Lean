import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Push

/-! # Integer ideals form a neighborhood basis in an infinite compact ring with dense integers -/

namespace Dubon2026

noncomputable section
open Filter Set Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [Infinite R]

omit [T2Space R] in
/-- Every open identity neighborhood in an infinite compact ring contains a nonzero point. -/
theorem compactRing_open_zero_nonzero (V : Set R) (hV : IsOpen V) (h0 : (0 : R) ∈ V) :
    ∃ x ∈ V, x ≠ 0 := by
  by_contra h
  push Not at h
  have he : V = {0} := by
    ext x
    exact ⟨fun hx => h x hx, fun hx => (Set.mem_singleton_iff.mp hx) ▸ h0⟩
  haveI : DiscreteTopology R := discreteTopology_iff_isOpen_singleton_zero.mpr (he ▸ hV)
  haveI : Finite R := finite_of_compact_of_discrete
  exact not_finite R

/-- Dense ordinary integers supply a nonzero integer in every original identity neighborhood of the compact ring. -/
theorem compactRing_dense_integer_small (hd : DenseRange (Int.cast : ℤ → R))
    (V : Set R) (hV : V ∈ 𝓝 (0 : R)) : ∃ n : ℤ, n ≠ 0 ∧ (n : R) ∈ V := by
  obtain ⟨W, hWV, hWo, h0⟩ := mem_nhds_iff.mp hV
  obtain ⟨x, hx, hx0⟩ := compactRing_open_zero_nonzero W hWo h0
  obtain ⟨n, hn⟩ := hd.exists_mem_open (hWo.inter isClosed_singleton.isOpen_compl)
    ⟨x, hx, hx0⟩
  refine ⟨n, ?_, hWV hn.1⟩
  intro hn0
  exact hn.2 (by simp [hn0])

/-- A single nonzero original integer sends the entire compact ring into any prescribed identity neighborhood. -/
theorem compactRing_integer_ideal_small (hd : DenseRange (Int.cast : ℤ → R))
    (U : Set R) (hU : U ∈ 𝓝 (0 : R)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x : R, (n : R) * x ∈ U := by
  have he : ∀ᶠ a : R in 𝓝 0, ∀ x ∈ (Set.univ : Set R), a * x ∈ U := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro x _
    have hm : ContinuousAt (fun z : R × R => z.1 * z.2) (0, x) := continuous_mul.continuousAt
    exact hm (by simpa only [zero_mul] using hU)
  obtain ⟨n, hn, hnv⟩ := compactRing_dense_integer_small hd _ he
  exact ⟨n, hn, fun x => hnv x (Set.mem_univ x)⟩

/-- Positive ordinary integer ideals are cofinal among all identity neighborhoods of the original compact ring. -/
theorem compactRing_positive_integer_ideal_small (hd : DenseRange (Int.cast : ℤ → R))
    (U : Set R) (hU : U ∈ 𝓝 (0 : R)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x : R, (D : R) * x ∈ U := by
  obtain ⟨n, hn, hsmall⟩ := compactRing_integer_ideal_small hd U hU
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩
  intro x
  rcases le_total 0 n with hpos | hneg
  · have he : (n.natAbs : R) = (n : R) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos]
    rw [he]
    exact hsmall x
  · have he : (n.natAbs : R) = -(n : R) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg]
    rw [he, neg_mul, ← mul_neg]
    exact hsmall (-x)

end
end Dubon2026
