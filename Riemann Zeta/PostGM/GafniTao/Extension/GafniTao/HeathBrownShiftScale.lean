import GafniTao.HeathBrownRefinedCountChoice

/-!
# Source-scale bounds for the Heath-Brown shift cutoff

These lemmas remove the floor from `D` in the direction needed by the
published calculation, while preserving the literal finite cutoff in the
counting theorem itself.
-/

namespace GafniTao

noncomputable section

theorem heathBrownShiftBound_cast_le
    {N k H : ℕ} {lambda : ℝ} (hlambda : 0 < lambda) (hH : 0 < H) :
    (heathBrownShiftBound N k H lambda : ℝ) ≤
      4 * ((k - 1).factorial : ℝ) /
        (lambda * (H : ℝ) ^ (k - 1)) := by
  let x : ℝ := 4 * ((k - 1).factorial : ℝ) /
    (lambda * (H : ℝ) ^ (k - 1))
  let Q : ℕ := ⌊x⌋₊
  change ((min N Q : ℕ) : ℝ) ≤ x
  have hmin : min N Q ≤ Q := min_le_right _ _
  have hminCast : ((min N Q : ℕ) : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hmin
  have hxnonneg : 0 ≤ x := by dsimp only [x]; positivity
  have hfloor : (Q : ℝ) ≤ x := by
    dsimp only [Q]
    exact Nat.floor_le hxnonneg
  exact hminCast.trans hfloor

theorem inv_pow_succ_le_inv_pow
    {H r : ℕ} (hH : 1 ≤ H) :
    (((H : ℝ) ^ (r + 1))⁻¹) ≤ (((H : ℝ) ^ r)⁻¹) := by
  have hbase : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hpow : (H : ℝ) ^ r ≤ (H : ℝ) ^ (r + 1) :=
    pow_le_pow_right₀ hbase (Nat.le_succ r)
  exact inv_anti₀ (by positivity) hpow

theorem heathBrownShiftBound_cast_le_previous_power
    {N k H : ℕ} {lambda : ℝ}
    (hk : 3 ≤ k) (hlambda : 0 < lambda) (hH : 1 ≤ H) :
    (heathBrownShiftBound N k H lambda : ℝ) ≤
      4 * ((k - 1).factorial : ℝ) *
        (((H : ℝ) ^ (k - 2))⁻¹) / lambda := by
  have hD := heathBrownShiftBound_cast_le
    (N := N) (k := k) (H := H) hlambda (by omega)
  have hexp : k - 1 = (k - 2) + 1 := by omega
  have hinv : (((H : ℝ) ^ (k - 1))⁻¹) ≤
      (((H : ℝ) ^ (k - 2))⁻¹) := by
    rw [hexp]
    exact inv_pow_succ_le_inv_pow hH
  calc
    (heathBrownShiftBound N k H lambda : ℝ) ≤
        4 * ((k - 1).factorial : ℝ) /
          (lambda * (H : ℝ) ^ (k - 1)) := hD
    _ = 4 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 1))⁻¹) / lambda := by
      field_simp
    _ ≤ 4 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda := by
      gcongr

theorem heathBrown_shift_plus_c_le
    {N k H : ℕ} {lambda : ℝ}
    (hk : 3 ≤ k) (hlambda : 0 < lambda) (hH : 1 ≤ H) :
    let D := heathBrownShiftBound N k H lambda
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    (D : ℝ) + c ≤
      12 * ((k - 1).factorial : ℝ) *
        (((H : ℝ) ^ (k - 2))⁻¹) / lambda := by
  dsimp only
  have hD := heathBrownShiftBound_cast_le_previous_power
    (N := N) (k := k) (H := H) hk hlambda hH
  have hfactNat : (k - 2).factorial ≤ (k - 1).factorial :=
    Nat.factorial_le (by omega)
  have hfact : ((k - 2).factorial : ℝ) ≤ (k - 1).factorial := by
    exact_mod_cast hfactNat
  have hc :
      8 * ((k - 2).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda ≤
        8 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda := by
    gcongr
  calc
    (heathBrownShiftBound N k H lambda : ℝ) +
        8 * ((k - 2).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda ≤
      4 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda +
        8 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda := add_le_add hD hc
    _ = 12 * ((k - 1).factorial : ℝ) *
        (((H : ℝ) ^ (k - 2))⁻¹) / lambda := by ring

theorem heathBrown_b_plus_aD_le
    {N k H : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hH : 8 ≤ H) :
    let D := heathBrownShiftBound N k H lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    b + a * D ≤
      4 + 4 * A * (k - 1 : ℕ) * N *
        (((H : ℝ) ^ (k - 1))⁻¹) := by
  dsimp only
  have hHpos : 0 < H := by omega
  have hpowLower : (8 : ℝ) ≤ (H : ℝ) ^ (k - 2) := by
    have hHone : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
    have hHcast : (8 : ℝ) ≤ H := by exact_mod_cast hH
    have hpow : (H : ℝ) ≤ (H : ℝ) ^ (k - 2) := by
      simpa only [pow_one] using
        pow_le_pow_right₀ hHone (by omega : 1 ≤ k - 2)
    exact hHcast.trans hpow
  have hpowPos : 0 < (H : ℝ) ^ (k - 2) := by positivity
  have hb : 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3 ≤ 4 := by
    have h8div : 8 / ((H : ℝ) ^ (k - 2)) ≤ 1 := by
      rw [div_le_iff₀ hpowPos]
      simpa only [one_mul] using hpowLower
    rw [← div_eq_mul_inv]
    linarith
  have hD := heathBrownShiftBound_cast_le
    (N := N) (k := k) (H := H) hlambda hHpos
  have ha : 0 ≤ A * lambda * (N : ℝ) /
      ((k - 2).factorial : ℝ) := by positivity
  have haD := mul_le_mul_of_nonneg_left hD ha
  have hfactNat : (k - 1).factorial =
      (k - 1) * (k - 2).factorial := by
    conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega,
      Nat.factorial_succ]
    rw [show k - 2 + 1 = k - 1 by omega]
  have hfact : ((k - 1).factorial : ℝ) =
      (k - 1 : ℕ) * ((k - 2).factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hsimplify :
      (A * lambda * (N : ℝ) / ((k - 2).factorial : ℝ)) *
          (4 * ((k - 1).factorial : ℝ) /
            (lambda * (H : ℝ) ^ (k - 1))) =
        4 * A * (k - 1 : ℕ) * N *
          (((H : ℝ) ^ (k - 1))⁻¹) := by
    rw [hfact]
    field_simp
  rw [hsimplify] at haD
  exact add_le_add hb haD

#print axioms heathBrownShiftBound_cast_le
#print axioms inv_pow_succ_le_inv_pow
#print axioms heathBrownShiftBound_cast_le_previous_power
#print axioms heathBrown_shift_plus_c_le
#print axioms heathBrown_b_plus_aD_le

end

end GafniTao
