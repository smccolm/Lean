import Dubon2026.SourceCellSideLocality

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
noncomputable section
open scoped Real
open Set

theorem arcSet_eq_rightUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) (a : Fin R.N) (ha : a.val = 0) :
    R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  subst hy
  exact (arcData_of_isSquare h).arc0 a ha

theorem arcSet_eq_rightLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) (a : Fin R.N) (ha : a.val = 5) :
    R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  subst hy
  exact (arcData_of_isSquare h).arc5 a ha

theorem arcSet_eq_leftUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) (a : Fin R.N) (ha : a.val = 2) :
    R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  subst hy
  exact (arcData_of_isSquare h).arc2 a ha

theorem arcSet_eq_leftLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) (a : Fin R.N) (ha : a.val = 3) :
    R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  subst hy
  exact (arcData_of_isSquare h).arc3 a ha

theorem arcSet_eq_bottom {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) (a : Fin R.N) (ha : a.val = 4) :
    R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} :=
  (arcData_of_isSquare h).arc4 a ha

theorem arcSet_eq_top {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) (a : Fin R.N) (ha : a.val = 1) :
    R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} :=
  (arcData_of_isSquare h).arc1 a ha

theorem exists_arcSet_eq_rightUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) :
    ∃ a : Fin R.N, a.val = 0 ∧
      R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨0, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_rightUpper h hy _ rfl

theorem exists_arcSet_eq_rightLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) :
    ∃ a : Fin R.N, a.val = 5 ∧
      R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨5, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_rightLower h hy _ rfl

theorem exists_arcSet_eq_leftUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) :
    ∃ a : Fin R.N, a.val = 2 ∧
      R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨2, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_leftUpper h hy _ rfl

theorem exists_arcSet_eq_leftLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) :
    ∃ a : Fin R.N, a.val = 3 ∧
      R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨3, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_leftLower h hy _ rfl

theorem exists_arcSet_eq_bottom {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) :
    ∃ a : Fin R.N, a.val = 4 ∧
      R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨4, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_bottom h _ rfl

theorem exists_arcSet_eq_top {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) :
    ∃ a : Fin R.N, a.val = 1 ∧
      R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨1, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_top h _ rfl


end
end Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
