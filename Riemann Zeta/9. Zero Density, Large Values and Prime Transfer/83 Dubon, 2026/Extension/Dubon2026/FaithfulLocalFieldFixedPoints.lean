import Dubon2026.FaithfulFieldUnitHilbert90
import Dubon2026.NormedLocalFieldCyclicCohomology
import Mathlib.Topology.Algebra.Field

/-! # The actual fixed field of a finite norm-preserving local action

The fixed subfield is closed in the original local field. A product of
conjugates supplies an element with nontrivial norm in that same fixed
field. These discharge the local-field hypotheses of the already proved
cyclic H2 order theorem, without constructing another completion model.
This is a dependency of DUB-17's original local idele factor computation.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators
variable (G F : Type) [Group G] [Finite G] [NontriviallyNormedField F]
  [MulSemiringAction G F]
  (hnorm : ∀ (g : G) (x : F), ‖g • x‖ = ‖x‖)

omit [Finite G] in
include hnorm in
/-- The actual fixed field is closed in the original norm topology. -/
theorem normPreserving_fixedField_isClosed :
    IsClosed ((FixedPoints.subfield G F : Subfield F) : Set F) := by
  have hc (g : G) : Continuous (fun x : F => g • x) := by
    apply Isometry.continuous
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← smul_sub, hnorm]
  have he : ((FixedPoints.subfield G F : Subfield F) : Set F) =
      ⋂ g : G, {x : F | g • x = x} := by
    ext x
    simp [FixedPoints.subfield, MulAction.mem_fixedPoints]
  rw [he]
  exact isClosed_iInter (fun g => isClosed_eq (hc g) continuous_id)

include hnorm in
/-- A genuine conjugate product gives nontrivial norm in the actual fixed field. -/
theorem normPreserving_fixedField_exists_norm_gt_one :
    ∃ x : FixedPoints.subfield G F, 1 < ‖x‖ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm F
  let y : F := ∏ g : G, g • x
  have hy : y ∈ FixedPoints.subfield G F := by
    intro g
    change g • (∏ h : G, h • x) = ∏ h : G, h • x
    rw [Finset.smul_prod']
    simp_rw [smul_smul]
    exact Equiv.prod_comp (Equiv.mulLeft g) (fun h : G => h • x)
  refine ⟨⟨y, hy⟩, ?_⟩
  change 1 < ‖∏ g : G, g • x‖
  rw [norm_prod]
  simp_rw [hnorm]
  simpa using one_lt_pow₀ hx (Fintype.card_ne_zero : Fintype.card G ≠ 0)

end
end Dubon2026
