import Dubon2026.PositiveAdelicGL2Continuity
import Mathlib.Topology.Piecewise

/-! # Actual rational sign correction for both real components of GL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped MatrixGroups

/-- The original rational general-linear group maps to its actual real matrices. -/
def rationalGL2ToReal : GeneralLinearGroup (Fin 2) ℚ →* GeneralLinearGroup (Fin 2) ℝ :=
  GeneralLinearGroup.map (Rat.castHom ℝ)

/-- The original rational general-linear group maps diagonally to its actual finite adelic matrices. -/
def rationalGL2ToFinite :
    GeneralLinearGroup (Fin 2) ℚ →* GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))

/-- Positivity of the original rational determinant is equivalent to positivity at the real place. -/
theorem rationalGL2ToReal_positive_iff (g : GeneralLinearGroup (Fin 2) ℚ) :
    rationalGL2ToReal g ∈ GLPos (Fin 2) ℝ ↔ g ∈ GLPos (Fin 2) ℚ := by
  change 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (Rat.castHom ℝ) g)).val ↔ _
  rw [GeneralLinearGroup.map_det]
  change 0 < ((GeneralLinearGroup.det g).val : ℝ) ↔ 0 < (GeneralLinearGroup.det g).val
  exact_mod_cast Iff.rfl

/-- The positive real component of the actual invertible matrix group is both open and closed. -/
theorem realGL2_positive_isClopen :
    IsClopen (GLPos (Fin 2) ℝ : Set (GeneralLinearGroup (Fin 2) ℝ)) := by
  have hc : Continuous (fun g : GeneralLinearGroup (Fin 2) ℝ => (GeneralLinearGroup.det g).val) :=
    Units.continuous_val.matrix_det
  refine ⟨?_, isOpen_lt continuous_const hc⟩
  have he : (GLPos (Fin 2) ℝ : Set (GeneralLinearGroup (Fin 2) ℝ)) =
      {g | 0 ≤ (GeneralLinearGroup.det g).val} := by
    ext g
    change 0 < (GeneralLinearGroup.det g).val ↔ 0 ≤ (GeneralLinearGroup.det g).val
    exact lt_iff_le_and_ne.trans (and_iff_left (Ne.symm (Units.ne_zero (GeneralLinearGroup.det g))))
  rw [he]
  exact isClosed_le continuous_const hc

/-- The literal rational reflection has determinant minus one. -/
def rationalGL2Reflection : GeneralLinearGroup (Fin 2) ℚ :=
  gl2UnitFirstDiagonal (-1 : ℚˣ)

/-- Its real determinant is exactly minus one. -/
theorem rationalGL2Reflection_real_det :
    (GeneralLinearGroup.det (rationalGL2ToReal rationalGL2Reflection)).val = -1 := by
  rw [rationalGL2ToReal, GeneralLinearGroup.map_det, rationalGL2Reflection,
    gl2UnitFirstDiagonal_det]
  norm_num

/-- Select the identity or the actual rational reflection according to the original real determinant. -/
def realGL2RationalSign (g : GeneralLinearGroup (Fin 2) ℝ) : GeneralLinearGroup (Fin 2) ℚ :=
  if 0 < (GeneralLinearGroup.det g).val then 1 else rationalGL2Reflection

/-- The rational sign correction gives a genuinely positive real matrix for every original invertible matrix. -/
theorem realGL2RationalSign_positive (g : GeneralLinearGroup (Fin 2) ℝ) :
    (rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g ∈ GLPos (Fin 2) ℝ := by
  unfold realGL2RationalSign
  split_ifs with hg
  · simpa using hg
  · change 0 < (GeneralLinearGroup.det
      ((rationalGL2ToReal rationalGL2Reflection)⁻¹ * g)).val
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      rationalGL2Reflection_real_det]
    have hn : (GeneralLinearGroup.det g).val < 0 :=
      lt_of_le_of_ne (le_of_not_gt hg) (Units.ne_zero _)
    simpa using neg_pos.mpr hn

/-- The actual positive real component chosen by rational left translation. -/
def realGL2PositivePart (g : GeneralLinearGroup (Fin 2) ℝ) : GL(2, ℝ)⁺ :=
  ⟨(rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g, realGL2RationalSign_positive g⟩

/-- Every function of the two-valued rational correction is continuous in the original real matrix. -/
theorem realGL2RationalSign_function_continuous {A : Type*} [TopologicalSpace A]
    (F : GeneralLinearGroup (Fin 2) ℚ → A) :
    Continuous (fun g => F (realGL2RationalSign g)) := by
  classical
  simp only [realGL2RationalSign, apply_ite]
  apply Continuous.if _ continuous_const continuous_const
  intro g hg
  have he : frontier {g : GeneralLinearGroup (Fin 2) ℝ | 0 < (GeneralLinearGroup.det g).val} = ∅ :=
    realGL2_positive_isClopen.frontier_eq
  rw [he] at hg
  exact False.elim hg

/-- The actual positive real correction is continuous across the two disjoint real components. -/
theorem realGL2PositivePart_continuous : Continuous realGL2PositivePart :=
  ((realGL2RationalSign_function_continuous rationalGL2ToReal).inv.mul continuous_id).subtype_mk _

/-- On the positive component the rational correction is the identity. -/
theorem realGL2RationalSign_of_positive (g : GL(2, ℝ)⁺) : realGL2RationalSign g.val = 1 :=
  if_pos g.property

/-- On the positive component the actual corrected matrix is the original matrix. -/
theorem realGL2PositivePart_of_positive (g : GL(2, ℝ)⁺) : realGL2PositivePart g.val = g := by
  apply Subtype.ext
  change (rationalGL2ToReal (realGL2RationalSign g.val))⁻¹ * g.val = g.val
  rw [realGL2RationalSign_of_positive, map_one, inv_one, one_mul]

end
end Dubon2026
