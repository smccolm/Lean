import Dubon2026.CuspPointwiseRankinBound
import Dubon2026.SatakeSymmetricTrace

/-! # Quantitative bounds for the actual local roots from the Rankin remainder -/

namespace Dubon2026

noncomputable section

/-- A power bound for the actual homogeneous traces controls each of its two roots. -/
theorem satake_right_root_sq_le_of_trace_bound {α β : ℂ} {A B : ℝ}
    (hA : 1 ≤ A)
    (hb : ∀ r : ℕ, ‖satakeSymmetricTrace α β r‖ ^ 2 ≤ B * A ^ r) :
    ‖β‖ ^ 2 ≤ A := by
  have hA0 : 0 < A := by linarith
  by_contra h
  have hroot : A < ‖β‖ ^ 2 := lt_of_not_ge h
  have hq : 1 < ‖β‖ ^ 2 / A := (one_lt_div hA0).mpr hroot
  let C := 2 * B * (A + ‖α‖ ^ 2)
  have hbound : ∀ r : ℕ, (‖β‖ ^ 2 / A) ^ r ≤ C := by
    intro r
    have he : β ^ (r + 1) = satakeSymmetricTrace α β (r + 1) - α * satakeSymmetricTrace α β r := by
      linear_combination -(satakeSymmetricTrace_succ α β r)
    have hn := norm_sub_le (satakeSymmetricTrace α β (r + 1)) (α * satakeSymmetricTrace α β r)
    rw [← he, norm_mul] at hn
    have hs := mul_self_le_mul_self (norm_nonneg _) hn
    have hα := mul_le_mul_of_nonneg_left (hb r) (sq_nonneg ‖α‖)
    have hh : ‖β ^ (r + 1)‖ ^ 2 ≤ C * A ^ r := by
      have ht := hb (r + 1)
      rw [pow_succ A r] at ht
      dsimp [C]
      nlinarith [sq_nonneg (‖satakeSymmetricTrace α β (r + 1)‖ - ‖α‖ * ‖satakeSymmetricTrace α β r‖)]
    rw [norm_pow, ← pow_mul, Nat.mul_comm (r + 1) 2, pow_mul] at hh
    have hstep : (‖β‖ ^ 2) ^ r ≤ (‖β‖ ^ 2) ^ (r + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (sq_nonneg _) _) (by linarith)
    rw [div_pow, div_le_iff₀ (pow_pos hA0 r)]
    exact hstep.trans hh
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt C hq
  exact (not_lt_of_ge (hbound r)) hr

/-- The actual determinant-one symmetric trace is invariant under interchanging its two roots. -/
theorem satakeSymmetricTrace_swap {α β : ℂ} (hprod : α * β = 1) (r : ℕ) :
    satakeSymmetricTrace α β r = satakeSymmetricTrace β α r := by
  rw [satakeSymmetricTrace_chebyshev hprod,
    satakeSymmetricTrace_chebyshev (by simpa only [mul_comm] using hprod), add_comm α β]

/-- Both roots inherit the same square bound from the actual coefficient trace growth. -/
theorem satake_roots_sq_le_of_trace_bound {α β : ℂ} {A B : ℝ}
    (hprod : α * β = 1) (hA : 1 ≤ A)
    (hb : ∀ r : ℕ, ‖satakeSymmetricTrace α β r‖ ^ 2 ≤ B * A ^ r) :
    ‖α‖ ^ 2 ≤ A ∧ ‖β‖ ^ 2 ≤ A := by
  refine ⟨satake_right_root_sq_le_of_trace_bound (α := β) (B := B) hA ?_,
    satake_right_root_sq_le_of_trace_bound hA hb⟩
  intro r
  rw [← satakeSymmetricTrace_swap hprod]
  exact hb r

/-- The proved three-fifths Rankin remainder bounds the squares of both genuine good-prime Satake roots by p^(3/5). This is weaker than Deligne purity. -/
theorem primitiveSatake_norm_sq_le_three_fifths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖primitiveSatakePlus f p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ) ∧
      ‖primitiveSatakeMinus f p‖ ^ 2 ≤ (p : ℝ) ^ (3 / 5 : ℝ) := by
  obtain ⟨B, _hB, hb⟩ := exists_normalized_cusp_coefficient_three_fifths f.toCuspForm hk
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply satake_roots_sq_le_of_trace_bound (B := B) (primitiveSatake_trace_det f p).2
    (Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) (by norm_num))
  intro r
  rw [← primitive_primePower_eq_satakeTrace f hp hpQ]
  have ht := hb (p ^ r) (Nat.one_le_pow r p hp.pos)
  rwa [Nat.cast_pow, ← Real.rpow_natCast_mul hp0.le, mul_comm (r : ℝ),
    Real.rpow_mul_natCast hp0.le] at ht

end
end Dubon2026
