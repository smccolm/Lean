import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Passing arithmetic double-coset finiteness to an original open level

A compact level with finite arithmetic double-coset quotient has finite
quotient after replacement by any original open level. The intersection
inside the compact level has finite index by the native topological
quotient theorem. This is exactly the transfer needed for DUB-17's
prescribed unitary levels after the integral-level class theorem.
-/

namespace Dubon2026

noncomputable section

/-- A finite arithmetic double-coset quotient at one compact level is finite at every original open level. -/
theorem doubleCoset_finite_of_compact_level {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ V U : Subgroup G)
    (hV : IsCompact (V : Set G)) (hU : IsOpen (U : Set G))
    [Finite (DoubleCoset.Quotient (G := G) Γ V)] :
    Finite (DoubleCoset.Quotient (G := G) Γ U) := by
  classical
  let W := U.subgroupOf V
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  letI : Finite (V ⧸ W) := W.quotient_finite_of_isOpen (hU.preimage continuous_subtype_val)
  let f : DoubleCoset.Quotient (G := G) Γ V × (V ⧸ W) →
      DoubleCoset.Quotient (G := G) Γ U :=
    fun p => DoubleCoset.mk Γ U (p.1.out * (p.2.out : G))
  apply Finite.of_surjective f
  intro z
  let q : DoubleCoset.Quotient (G := G) Γ V := DoubleCoset.mk Γ V z.out
  have hq : DoubleCoset.mk Γ V q.out = DoubleCoset.mk Γ V z.out :=
    DoubleCoset.out_eq' Γ V q
  obtain ⟨a, ha, b, hb, he⟩ := (DoubleCoset.eq Γ V q.out z.out).mp hq
  let bv : V := ⟨b, hb⟩
  let r : V ⧸ W := QuotientGroup.mk bv
  have hr : r.out⁻¹ * bv ∈ W := QuotientGroup.eq.mp (QuotientGroup.out_eq' r)
  refine ⟨(q, r), ?_⟩
  change DoubleCoset.mk Γ U (q.out * (r.out : G)) = z
  rw [← DoubleCoset.out_eq' Γ U z]
  apply (DoubleCoset.eq Γ U _ z.out).mpr
  refine ⟨a, ha, ((r.out⁻¹ * bv : V) : G), hr, ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left, bv] using he

end
end Dubon2026
