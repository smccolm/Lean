import GafniTao.WooleySection7HardArithmetic
import GafniTao.WooleyTwoFactorHolder

/-!
# Exponent identities for Wooley Section 8

The identities below are the exact exponent bookkeeping behind equations
(8.1) and (8.2).  They are stated separately from Hölder so that no
subtraction cast or endpoint case is implicit in the analytic proof.
-/

namespace GafniTao

noncomputable section

theorem wooleyTriangular_cast (r : ℕ) :
    (wooleyTriangular r : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
  unfold wooleyTriangular
  rw [Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self r))
    (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  rfl

theorem wooleyTriangular_mono {a b : ℕ} (hab : a ≤ b) :
    wooleyTriangular a ≤ wooleyTriangular b := by
  unfold wooleyTriangular
  exact Nat.div_le_div_right
    (Nat.mul_le_mul hab (Nat.add_le_add_right hab 1))

theorem wooleyTriangular_sub_le (k r : ℕ) :
    wooleyTriangular (k - r) ≤ wooleyTriangular k :=
  wooleyTriangular_mono (Nat.sub_le k r)

theorem wooleyTriangular_pred_le {k r : ℕ} (hrk : r ≤ k) :
    wooleyTriangular (r - 1) ≤ wooleyTriangular k :=
  wooleyTriangular_mono ((Nat.sub_le r 1).trans hrk)

/-- The exponent of the `b'`-residue factor in the Section 8 interpolation. -/
theorem wooley_section8_left_exponent
    {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (2 * ((wooleyTriangular k - wooleyTriangular (k - r) : ℕ) : ℝ)) +
        ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) *
          (2 * (wooleyTriangular (r - 1) : ℝ)) =
      2 * (wooleyTriangular r : ℝ) := by
  have hsub := wooleyTriangular_sub_le k r
  have hpred := wooleyTriangular_pred_le (show r ≤ k by omega)
  rw [Nat.cast_sub hsub, wooleyTriangular_cast,
    wooleyTriangular_cast, wooleyTriangular_cast,
    wooleyTriangular_cast]
  push_cast
  rw [Nat.cast_sub hrk.le, Nat.cast_sub hr]
  have hkr : (r : ℝ) < k := by exact_mod_cast hrk
  have hd' : (1 + (k : ℝ) - r) ≠ 0 := by linarith
  calc
    _ = (((r : ℝ) + (r : ℝ) ^ 2) * (1 + (k : ℝ) - r)) *
          (1 + (k : ℝ) - r)⁻¹ := by ring
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hd', mul_one]; ring

/-- The exponent of the `b`-residue factor in the Section 8 interpolation. -/
theorem wooley_section8_right_exponent
    {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (2 * (wooleyTriangular (k - r) : ℝ)) +
        ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) *
          (2 * ((wooleyTriangular k - wooleyTriangular (r - 1) : ℕ) : ℝ)) =
      2 * ((wooleyTriangular k - wooleyTriangular r : ℕ) : ℝ) := by
  have hsub := wooleyTriangular_sub_le k r
  have hpred := wooleyTriangular_pred_le (show r ≤ k by omega)
  have hrTri : wooleyTriangular r ≤ wooleyTriangular k :=
    wooleyTriangular_mono (show r ≤ k by omega)
  rw [Nat.cast_sub hpred, Nat.cast_sub hrTri,
    wooleyTriangular_cast, wooleyTriangular_cast,
    wooleyTriangular_cast, wooleyTriangular_cast]
  push_cast
  rw [Nat.cast_sub hrk.le, Nat.cast_sub hr]
  have hkr : (r : ℝ) < k := by exact_mod_cast hrk
  have hd' : (1 + (k : ℝ) - r) ≠ 0 := by linarith
  calc
    _ = (((k : ℝ) + (k : ℝ) ^ 2 - r - (r : ℝ) ^ 2) *
          (1 + (k : ℝ) - r)) * (1 + (k : ℝ) - r)⁻¹ := by ring
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hd', mul_one]; ring

theorem wooley_section8_weight_complement
    {k r : ℕ} (hrk : r < k) :
    1 - 1 / ((k - r + 1 : ℕ) : ℝ) =
      ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < (k - r + 1 : ℕ) := by positivity
  field_simp [ne_of_gt hd]
  push_cast
  rw [Nat.cast_sub hrk.le]
  ring

#print axioms wooleyTriangular_cast
#print axioms wooleyTriangular_mono
#print axioms wooley_section8_left_exponent
#print axioms wooley_section8_right_exponent
#print axioms wooley_section8_weight_complement

end

end GafniTao
