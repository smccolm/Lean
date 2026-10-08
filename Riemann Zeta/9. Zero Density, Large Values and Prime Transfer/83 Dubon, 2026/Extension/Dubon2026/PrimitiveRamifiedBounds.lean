import Dubon2026.PrimitiveFirstSymmetricL
import Dubon2026.CuspNormalizedEnergy

/-! # Actual ramified factors are nonzero across the prime-distribution boundary -/

namespace Dubon2026

noncomputable section

/-- The already proved linear energy estimate bounds each actual normalized coefficient square. -/
theorem exists_normalized_cusp_coefficient_square_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (hk : 0 < k) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ‖normalizedCuspCoefficients f n‖ ^ 2 ≤ B * n := by
  obtain ⟨B,hB,hbound⟩ := exists_normalized_cusp_square_upper f hk
  refine ⟨B,hB,fun n hn => ?_⟩
  exact (Finset.single_le_sum (fun m _ => sq_nonneg ‖normalizedCuspCoefficients f m‖)
    (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩)).trans (hbound n)

/-- The genuine ramified prime-power law and linear energy estimate bound the actual local root by sqrt(p), without Deligne. -/
theorem primitive_bad_coefficient_norm_sq_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 ≤ (p : ℝ) := by
  obtain ⟨B,_hB,hbound⟩ := exists_normalized_cusp_coefficient_square_upper f.toCuspForm hk
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : ∀ r : ℕ, (‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 / (p : ℝ)) ^ r ≤ B := by
    intro r
    have ht := hbound (p ^ r) (Nat.one_le_pow r p hp.pos)
    rw [primitiveCuspForm_normalized_bad_prime_power f hp hpQ, norm_pow, Nat.cast_pow] at ht
    rw [div_pow, div_le_iff₀ (pow_pos hp0 r)]
    rw [← pow_mul, Nat.mul_comm 2 r, pow_mul]
    exact ht
  have hr : ‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 / (p : ℝ) ≤ 1 := by
    by_contra h
    obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt B (lt_of_not_ge h)
    exact (not_lt_of_ge (hb r)) hr
  exact (div_le_one hp0).mp hr

/-- The actual ramified prime term has norm below one on Re(s)>1/2. -/
theorem norm_primitive_bad_prime_term_lt_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hb : ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (primitive_bad_coefficient_norm_sq_le f hk hp hpQ)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (1 / 2 - s.re) := by rw [← Real.rpow_add hp0, sub_eq_add_neg]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- Every actual ramified Euler denominator is nonzero on a neighborhood of the full line Re(s)=1. -/
theorem primitive_bad_euler_denominator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 1 / 2 < s.re) : primitiveEulerDenominator f p s ≠ 0 := by
  rw [primitiveEulerDenominator, if_pos hpQ, add_zero]
  intro hz
  have he := sub_eq_zero.mp hz
  have hn := norm_primitive_bad_prime_term_lt_one f hk hp hpQ hs
  rw [← he, norm_one] at hn
  exact lt_irrefl _ hn

/-- The literal finite bad-prime correction is nonzero throughout Re(s)>1/2. -/
theorem primitive_ramified_correction_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact primitive_bad_euler_denominator_ne_zero f hk p.property
    ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mp hp) hs

/-- Removing precisely the ramified factors preserves the actual holomorphic nonvanishing continuation requirement at order one. Neither continuation is assumed inside the form or Euler function. -/
theorem primitive_first_nonvanishing_continuation_iff {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f 1) {s | 1 < s.re}) ↔
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (LSeries (normalizedCuspCoefficients f.toCuspForm)) {s | 1 < s.re}) := by
  let C : ℂ → ℂ := fun s => ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s
  have hCd : Differentiable ℂ C :=
    fun _ => DifferentiableAt.fun_finsetProd (fun p _ => primitiveEulerDenominator_differentiable f p _)
  have hCa : AnalyticOnNhd ℂ C {s : ℂ | 1 ≤ s.re} := fun s _ => hCd.analyticAt s
  have hCn : ∀ s : ℂ, 1 ≤ s.re → C s ≠ 0 :=
    fun _ hs => primitive_ramified_correction_ne_zero f hk (by linarith)
  constructor
  · rintro ⟨F,hFa,hFn,hFe⟩
    refine ⟨fun s => F s / C s, hFa.div hCa hCn,
      fun s hs => div_ne_zero (hFn s hs) (hCn s hs), ?_⟩
    intro s hs
    dsimp only
    rw [hFe hs, primitive_first_symmetric_eq_cusp_lseries f hk.le hs]
    exact mul_div_cancel_right₀ _ (hCn s hs.le)
  · rintro ⟨F,hFa,hFn,hFe⟩
    refine ⟨fun s => F s * C s, hFa.mul hCa,
      fun s hs => mul_ne_zero (hFn s hs) (hCn s hs), ?_⟩
    intro s hs
    dsimp only
    rw [hFe hs, primitive_first_symmetric_eq_cusp_lseries f hk.le hs]

end
end Dubon2026
