import Dubon2026.RankinSatakeBounds

/-! # The original Rankin estimate excludes exceptional local principal-series parameters -/

namespace Dubon2026

noncomputable section

/-- The proved Rankin bound places each actual local Satake root strictly inside the square-root-prime boundary, without invoking Deligne. -/
theorem primitiveSatake_norm_sq_lt_prime {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    ‖primitiveSatakePlus F p‖ ^ 2 < p ∧ ‖primitiveSatakeMinus F p‖ ^ 2 < p := by
  have hb := primitiveSatake_norm_sq_le_three_fifths F hk hp hpN
  have hpow : (p : ℝ) ^ (3 / 5 : ℝ) < p := by
    calc
      _ < (p : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp.one_lt) (by norm_num)
      _ = p := Real.rpow_one _
  exact ⟨hb.1.trans_lt hpow, hb.2.trans_lt hpow⟩

/-- Neither original local Satake root has square equal to the original prime. -/
theorem primitiveSatake_square_ne_prime {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    primitiveSatakePlus F p ^ 2 ≠ (p : ℂ) ∧ primitiveSatakeMinus F p ^ 2 ≠ (p : ℂ) := by
  have hb := primitiveSatake_norm_sq_lt_prime F hk hp hpN
  constructor
  · intro he
    have hn := congrArg norm he
    simp only [norm_pow, Complex.norm_natCast] at hn
    exact (ne_of_lt hb.1) hn
  · intro he
    have hn := congrArg norm he
    simp only [norm_pow, Complex.norm_natCast] at hn
    exact (ne_of_lt hb.2) hn

/-- The original quotient of local Satake parameters avoids both exceptional unramified principal-series ratios, as a consequence of the already proved Rankin remainder. -/
theorem primitiveSatake_non_special {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    primitiveSatakePlus F p / primitiveSatakeMinus F p ≠ (p : ℂ) ∧
      primitiveSatakePlus F p / primitiveSatakeMinus F p ≠ (p : ℂ)⁻¹ := by
  have hprod := (primitiveSatake_trace_det F p).2
  have hn : primitiveSatakeMinus F p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact zero_ne_one hprod
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hs := primitiveSatake_square_ne_prime F hk hp hpN
  constructor
  · intro he
    have h := (div_eq_iff hn).mp he
    apply hs.1
    linear_combination primitiveSatakePlus F p * h + (p : ℂ) * hprod
  · intro he
    have h := (div_eq_iff hn).mp he
    have h' : primitiveSatakeMinus F p = (p : ℂ) * primitiveSatakePlus F p := by
      rw [h, mul_inv_cancel_left₀ hp0]
    apply hs.2
    linear_combination primitiveSatakeMinus F p * h' + (p : ℂ) * hprod

end
end Dubon2026
