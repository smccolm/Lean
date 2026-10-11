import Dubon2026.CompactSubmonoidInverse
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.Ring

/-! # Actual compact unit subgroups attached to original small additive lattices -/

namespace Dubon2026
noncomputable section

variable {L : Type*} [Field L] [TopologicalSpace L]
  [IsTopologicalDivisionRing L] [T2Space L]
  (A : AddSubgroup L) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)

/-- The original field units whose literal difference from one lies in the
original additive lattice form a submonoid by the actual product identity. -/
def latticeUnitSubmonoid : Submonoid Lˣ where
  carrier := {u | (u : L) - 1 ∈ A}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    change (u : L) * (v : L) - 1 ∈ A
    have he : (u : L) * (v : L) - 1 =
        ((u : L) - 1) + ((v : L) - 1) + ((u : L) - 1) * ((v : L) - 1) := by ring
    rw [he]
    exact A.add_mem (A.add_mem hu hv) (hmul _ hu _ hv)

omit [T2Space L] in
/-- The original unit submonoid is the continuous image of the original
compact additive lattice under `a ↦ 1+a`. Nonvanishing is explicit and is
discharged for a genuine small local-field lattice by its maximal-ideal containment. -/
theorem latticeUnitSubmonoid_isCompact
    (hA : IsCompact (A : Set L)) (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0) :
    IsCompact (latticeUnitSubmonoid A hmul : Set Lˣ) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let φ : A → Lˣ := fun x => Units.mk0 (1 + (x : L)) (hunit x x.property)
  have hφ : Continuous φ := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_const.add continuous_subtype_val
    · change Continuous (fun x : A => (1 + (x : L))⁻¹)
      exact (continuous_const.add continuous_subtype_val).inv₀
        (fun x => hunit x x.property)
  have he : Set.range φ = (latticeUnitSubmonoid A hmul : Set Lˣ) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      change (1 + (x : L)) - 1 ∈ A
      simpa only [add_sub_cancel_left] using x.property
    · intro hu
      refine ⟨⟨(u : L) - 1, hu⟩, ?_⟩
      apply Units.ext
      change 1 + ((u : L) - 1) = (u : L)
      ring
  rw [← he]
  exact isCompact_range hφ

include hmul in
/-- Inverses of original small-lattice units still differ from one by an
element of that same original lattice. Compact inverse closure supplies the
actual inverse; no inverse-closure certificate is assumed. -/
theorem latticeUnitSubmonoid_inverse_sub_one_mem
    (hA : IsCompact (A : Set L)) (hunit : ∀ x ∈ A, (1 : L) + x ≠ 0)
    (u : Lˣ) (hu : (u : L) - 1 ∈ A) :
    ((u⁻¹ : Lˣ) : L) - 1 ∈ A := by
  exact compactSubmonoid_inv_mem (latticeUnitSubmonoid A hmul)
    (latticeUnitSubmonoid_isCompact A hmul hA hunit) hu

end
end Dubon2026
