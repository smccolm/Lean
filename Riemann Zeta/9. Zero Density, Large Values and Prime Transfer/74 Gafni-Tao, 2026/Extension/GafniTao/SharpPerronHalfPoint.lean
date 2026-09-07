import GafniTao.SharpPerronGlobal

/-!
# Half-integral Perron evaluation points

The classical sharp Perron argument evaluates the contour at the midpoint of
the unit interval containing `x`.  This leaves `psi` unchanged and gives a
uniform distance of one half from every integer, avoiding any unrecorded
nearest-integer convention.
-/

namespace GafniTao

/-- The midpoint of the unit interval selected by the natural floor of `x`. -/
noncomputable def sharpPerronHalfPoint (x : ℝ) : ℝ :=
  (⌊x⌋₊ : ℝ) + 1 / 2

theorem sharpPerronHalfPoint_floor
    (x : ℝ) :
    ⌊sharpPerronHalfPoint x⌋₊ = ⌊x⌋₊ := by
  apply (Nat.floor_eq_iff (by
    rw [sharpPerronHalfPoint]
    positivity)).2
  constructor
  · rw [sharpPerronHalfPoint]
    norm_num
  · rw [sharpPerronHalfPoint]
    norm_num

theorem psi_sharpPerronHalfPoint
    (x : ℝ) :
    Chebyshev.psi (sharpPerronHalfPoint x) = Chebyshev.psi x := by
  simp only [Chebyshev.psi]
  rw [sharpPerronHalfPoint_floor]

theorem sharpPerronHalfPoint_sub_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |sharpPerronHalfPoint x - x| ≤ 1 / 2 := by
  have hfloorLe : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hxLt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  rw [abs_le, sharpPerronHalfPoint]
  constructor <;> linarith

theorem sharpPerronHalfPoint_pos
    (x : ℝ) :
    0 < sharpPerronHalfPoint x := by
  rw [sharpPerronHalfPoint]
  positivity

/-- Every integer is at least one half away from the midpoint evaluation
point. -/
theorem half_le_abs_sharpPerronHalfPoint_sub_natCast
    (x : ℝ) (n : ℕ) :
    1 / 2 ≤ |sharpPerronHalfPoint x - (n : ℝ)| := by
  rw [sharpPerronHalfPoint]
  rcases le_total n ⌊x⌋₊ with hnk | hkn
  · have hcast : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · by_cases heq : n = ⌊x⌋₊
    · subst n
      norm_num
    · have hsucc : ⌊x⌋₊ + 1 ≤ n := Nat.add_one_le_iff.mpr (lt_of_le_of_ne hkn (Ne.symm heq))
      have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsucc
      rw [abs_of_nonpos (by push_cast at hcast ⊢; linarith)]
      push_cast at hcast ⊢
      linarith

end GafniTao
