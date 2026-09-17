import Tao2026.LowFrequencyFourier

/-!
# Logarithmic absorption for low-frequency Fourier modes

This module turns the explicit conditional estimate from the low-frequency
PNT branch into an arbitrary logarithmic saving whenever the reciprocal-phase
scale is bounded by a fixed power of `log P`.
-/

open Complex Filter Set
open scoped Topology

namespace Tao2026

noncomputable section

/-- Every fixed nonnegative multiple of a fixed integral logarithmic power is
eventually bounded by the natural variable. -/
theorem eventually_const_mul_log_pow_le_natCast
    {C : ℝ} (hC : 0 ≤ C) (d : ℕ) :
    ∀ᶠ P : ℕ in atTop, C * (Real.log P) ^ d ≤ P := by
  by_cases hC0 : C = 0
  · subst C
    simp
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hsmall : (fun P : ℕ => (Real.log P) ^ d) =o[atTop]
      (fun P : ℕ => (P : ℝ)) := by
    simpa only [Function.comp_def] using
      (Real.isLittleO_pow_log_id_atTop (n := d)).comp_tendsto
        tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.bound (by positivity : (0 : ℝ) < C⁻¹),
    eventually_ge_atTop (1 : ℕ)] with P hbound hP
  have hlog : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hP)
  rw [Real.norm_of_nonneg (pow_nonneg hlog d),
    Real.norm_of_nonneg (Nat.cast_nonneg P)] at hbound
  have := mul_le_mul_of_nonneg_left hbound hC
  field_simp [hCpos.ne'] at this
  exact this

/-- Moving the quadratic reciprocal phase scale from `P` to `4P` loses at
most the uniform factor sixteen. -/
theorem reciprocalPhaseScale_le_sixteen_mul_at_four
    (N M : ℝ) {P : ℝ} (hP : 0 < P) :
    reciprocalPhaseScale N M 2 P ≤
      16 * reciprocalPhaseScale N M 2 (4 * P) := by
  unfold reciprocalPhaseScale
  norm_num [mul_pow]
  field_simp [hP.ne']
  nlinarith [abs_nonneg N, abs_nonneg M]

/-- Deterministic high/low phase-scale split.  Any proposed high threshold
whose factor-sixteen enlargement fits below the low cutoff gives one of the
two source regimes. -/
theorem reciprocalPhaseScale_low_or_high
    (N M P H : ℝ) (D : ℕ) (hP : 0 < P)
    (hbridge : 16 * H ≤ (Real.log P) ^ D) :
    reciprocalPhaseScale N M 2 P ≤ (Real.log P) ^ D ∨
      H ≤ reciprocalPhaseScale N M 2 (4 * P) := by
  by_cases hhigh : H ≤ reciprocalPhaseScale N M 2 (4 * P)
  · exact Or.inr hhigh
  · left
    have hcompare := reciprocalPhaseScale_le_sixteen_mul_at_four N M hP
    have hlt : reciprocalPhaseScale N M 2 (4 * P) < H := lt_of_not_ge hhigh
    linarith

/-- Every fixed real logarithmic threshold at a dyadic endpoint fits, after
the factor-sixteen scale change, below one fixed natural logarithmic power at
the left endpoint. -/
theorem exists_eventually_sixteen_mul_log_rpow_le_log_pow
    (d : ℝ) :
    ∃ D : ℕ, ∀ᶠ P : ℕ in atTop, ∀ b : ℕ,
      P ≤ b → b ≤ 2 * P →
      16 * (Real.log b) ^ d ≤ (Real.log P) ^ D := by
  let n := ⌈d⌉₊
  refine ⟨n + 2, ?_⟩
  have hlogSqTop : Tendsto (fun P : ℕ => (Real.log P) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstant : ∀ᶠ P : ℕ in atTop,
      16 * (2 : ℝ) ^ n ≤ (Real.log P) ^ 2 :=
    hlogSqTop.eventually (eventually_ge_atTop (16 * (2 : ℝ) ^ n))
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hconstant, hlogOne, eventually_ge_atTop (1 : ℕ)] with
      P hconstantP hlogP hP
  intro b hPb hbP
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast hP
  have hbpos : 0 < (b : ℝ) := hPpos.trans_le (by exact_mod_cast hPb)
  have hlogbOne : 1 ≤ Real.log (b : ℝ) :=
    hlogP.trans (Real.log_le_log hPpos (by exact_mod_cast hPb))
  have hlogTwoLe : Real.log 2 ≤ Real.log (P : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hlogbUpper : Real.log (b : ℝ) ≤ 2 * Real.log (P : ℝ) := by
    calc
      Real.log (b : ℝ) ≤ Real.log (2 * (P : ℝ)) :=
        Real.log_le_log hbpos (by exact_mod_cast hbP)
      _ = Real.log 2 + Real.log (P : ℝ) := by
        rw [Real.log_mul (by norm_num) hPpos.ne']
      _ ≤ 2 * Real.log (P : ℝ) := by linarith
  have hdn : d ≤ (n : ℝ) := by
    exact Nat.le_ceil d
  have hpower : (Real.log (b : ℝ)) ^ d ≤
      (2 * Real.log (P : ℝ)) ^ n := by
    calc
      (Real.log (b : ℝ)) ^ d ≤
          (Real.log (b : ℝ)) ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogbOne hdn
      _ = (Real.log (b : ℝ)) ^ n := Real.rpow_natCast _ _
      _ ≤ (2 * Real.log (P : ℝ)) ^ n := by
        exact pow_le_pow_left₀ (by positivity) hlogbUpper n
  calc
    16 * (Real.log b) ^ d ≤
        16 * (2 * Real.log P) ^ n := mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ = (16 * (2 : ℝ) ^ n) * (Real.log P) ^ n := by rw [mul_pow]; ring
    _ ≤ (Real.log P) ^ 2 * (Real.log P) ^ n := by
      exact mul_le_mul_of_nonneg_right hconstantP
        (pow_nonneg (zero_le_one.trans hlogP) n)
    _ = (Real.log P) ^ (n + 2) := by
      rw [show n + 2 = 2 + n by omega, pow_add]

/-- Uniform eventual high/low split in exactly the two normalizations consumed
by the low-frequency and high-frequency Fourier theorems. -/
theorem exists_eventually_reciprocalPhaseScale_low_or_log_rpow_high
    (d : ℝ) :
    ∃ D : ℕ, ∀ᶠ P : ℕ in atTop, ∀ (b : ℕ) (N M : ℝ),
      P ≤ b → b ≤ 2 * P →
      reciprocalPhaseScale N M 2 P ≤ (Real.log P) ^ D ∨
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2 (4 * P) := by
  obtain ⟨D, hbridge⟩ :=
    exists_eventually_sixteen_mul_log_rpow_le_log_pow d
  refine ⟨D, ?_⟩
  filter_upwards [hbridge, eventually_ge_atTop (1 : ℕ)] with P hbridgeP hP
  intro b N M hPb hbP
  exact reciprocalPhaseScale_low_or_high N M P ((Real.log b) ^ d) D
    (by exact_mod_cast hP) (hbridgeP b hPb hbP)

/-- Elementary absorption ledger for the explicit low-frequency bound. -/
theorem lowFrequencyExplicitMajorant_le_logSaving
    (C F P L : ℝ) (D S : ℕ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hL : 1 ≤ L)
    (hF : 0 ≤ F) (hFupper : F ≤ L ^ D)
    (hconstant : 312 * C ≤ L ^ 6)
    (hbridge : 75 * L ^ (D + S) ≤ P)
    (htail : 3 ≤ L ^ 2) :
    (1 / L +
        (2 * Real.pi * (3 * F) / L + 1 / L ^ 2)) *
          (4 * C * P / L ^ (D + S + 6)) +
        (2 * Real.pi * (3 * F) / L + 1 / L ^ 2) +
        P / L ^ (S + 2) ≤
      P / L ^ S := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLD : 1 ≤ L ^ D := one_le_pow₀ hL
  have hFinv : F / L ≤ L ^ D := by
    apply (div_le_iff₀ hLpos).2
    exact hFupper.trans (le_mul_of_one_le_right (pow_nonneg hLpos.le D) hL)
  have hpi : 2 * Real.pi * 3 ≤ 24 := by
    nlinarith [Real.pi_lt_four]
  have hphase : 2 * Real.pi * (3 * F) / L ≤ 24 * L ^ D := by
    calc
      2 * Real.pi * (3 * F) / L = (2 * Real.pi * 3) * (F / L) := by ring
      _ ≤ 24 * (F / L) :=
        mul_le_mul_of_nonneg_right hpi (div_nonneg hF hLpos.le)
      _ ≤ 24 * L ^ D := mul_le_mul_of_nonneg_left hFinv (by norm_num)
  have hinvSq : 1 / L ^ 2 ≤ 1 := by
    apply (div_le_one (pow_pos hLpos 2)).2
    exact one_le_pow₀ hL
  have herror :
      2 * Real.pi * (3 * F) / L + 1 / L ^ 2 ≤ 25 * L ^ D := by
    nlinarith
  have hinv : 1 / L ≤ 1 := by
    exact (div_le_one hLpos).2 hL
  have hfront :
      1 / L + (2 * Real.pi * (3 * F) / L + 1 / L ^ 2) ≤
        26 * L ^ D := by
    nlinarith
  have hBnonneg : 0 ≤ 4 * C * P / L ^ (D + S + 6) := by positivity
  have hpntRaw :
      (1 / L + (2 * Real.pi * (3 * F) / L + 1 / L ^ 2)) *
          (4 * C * P / L ^ (D + S + 6)) ≤
        26 * L ^ D * (4 * C * P / L ^ (D + S + 6)) :=
    mul_le_mul_of_nonneg_right hfront hBnonneg
  have hpntIdentity :
      26 * L ^ D * (4 * C * P / L ^ (D + S + 6)) =
        104 * C * P / L ^ (S + 6) := by
    field_simp [hLpos.ne', pow_add]
    ring
  have hpntAbsorb : 104 * C * P / L ^ (S + 6) ≤
      P / (3 * L ^ S) := by
    have hLSpos : 0 < L ^ S := pow_pos hLpos S
    have hL6pos : 0 < L ^ 6 := pow_pos hLpos 6
    rw [show L ^ (S + 6) = L ^ S * L ^ 6 by rw [pow_add]]
    apply (div_le_div_iff₀ (mul_pos hLSpos hL6pos)
      (mul_pos (by norm_num) hLSpos)).2
    have hmul := mul_le_mul_of_nonneg_right hconstant
      (mul_nonneg hP (pow_nonneg hLpos.le S))
    convert hmul using 1 <;> ring
  have hpnt :
      (1 / L + (2 * Real.pi * (3 * F) / L + 1 / L ^ 2)) *
          (4 * C * P / L ^ (D + S + 6)) ≤
        P / (3 * L ^ S) := by
    exact hpntRaw.trans (hpntIdentity.trans_le hpntAbsorb)
  have hbridgeAbsorb : 25 * L ^ D ≤ P / (3 * L ^ S) := by
    have hLSpos : 0 < L ^ S := pow_pos hLpos S
    apply (le_div_iff₀ (mul_pos (by norm_num) hLSpos)).2
    calc
      25 * L ^ D * (3 * L ^ S) = 75 * L ^ (D + S) := by
        rw [pow_add]
        ring
      _ ≤ P := hbridge
  have hbridge' :
      2 * Real.pi * (3 * F) / L + 1 / L ^ 2 ≤
        P / (3 * L ^ S) := herror.trans hbridgeAbsorb
  have htail' : P / L ^ (S + 2) ≤ P / (3 * L ^ S) := by
    have hLSpos : 0 < L ^ S := pow_pos hLpos S
    have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
    rw [show L ^ (S + 2) = L ^ S * L ^ 2 by rw [pow_add]]
    apply (div_le_div_iff₀ (mul_pos hLSpos hL2pos)
      (mul_pos (by norm_num) hLSpos)).2
    have hmul := mul_le_mul_of_nonneg_left htail
      (mul_nonneg hP (pow_nonneg hLpos.le S))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  calc
    _ ≤ P / (3 * L ^ S) + P / (3 * L ^ S) + P / (3 * L ^ S) := by
      gcongr
    _ = P / L ^ S := by ring

/-- Under the quantitative PNT contract, every Fourier mode whose reciprocal
phase scale is at most a fixed power of `log P` has an arbitrary fixed
logarithmic saving, uniformly on dyadic subintervals. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_primeFourierMode_sub_integral_Ico_le_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving) (D S : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P ≤
          (Real.log P) ^ D →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
          P / (Real.log P) ^ S := by
  obtain ⟨C, hC, hraw⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le
      (D + S + 6) ((S + 2 : ℕ) : ℝ)
  refine ⟨C, hC, ?_⟩
  have hlogPow6 : Tendsto (fun P : ℕ => (Real.log P) ^ 6) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstant : ∀ᶠ P : ℕ in atTop,
      312 * C ≤ (Real.log P) ^ 6 :=
    hlogPow6.eventually (eventually_ge_atTop (312 * C))
  have hbridge : ∀ᶠ P : ℕ in atTop,
      75 * (Real.log P) ^ (D + S) ≤ P :=
    eventually_const_mul_log_pow_le_natCast (by norm_num) (D + S)
  have hlogPow2 : Tendsto (fun P : ℕ => (Real.log P) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have htail : ∀ᶠ P : ℕ in atTop, 3 ≤ (Real.log P) ^ 2 :=
    hlogPow2.eventually (eventually_ge_atTop 3)
  have hlogOne : ∀ᶠ P : ℕ in atTop, 1 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hraw, hlogOne, hconstant, hbridge,
    htail, eventually_ge_atTop (1 : ℕ)] with P hrawP hlog hconstantP
      hbridgeP htailP hP
  intro a b q N M hPa hab hbP hFupper
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast hP
  have hlogpos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlog
  have hF : 0 ≤
      reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P :=
    reciprocalPhaseScale_nonneg _ _ _ hPpos
  have hmajor := lowFrequencyExplicitMajorant_le_logSaving
    C
    (reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P)
    (P : ℝ) (Real.log P) D S hC.le (Nat.cast_nonneg P) hlog hF
      hFupper hconstantP hbridgeP htailP
  calc
    ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        (1 / Real.log P +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ (D + S + 6)) +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2) +
          P * (Real.log P) ^ (-((S + 2 : ℕ) : ℝ)) :=
      hrawP a b q N M hPa hab hbP
    _ = (1 / Real.log P +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ (D + S + 6)) +
          (2 * Real.pi *
              (3 * reciprocalPhaseScale
                ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 P) /
              Real.log P +
            1 / (Real.log P) ^ 2) +
          P / (Real.log P) ^ (S + 2) := by
      rw [Real.rpow_neg hlogpos.le, Real.rpow_natCast]
      rfl
    _ ≤ P / (Real.log P) ^ S := hmajor

/-- Zero-mode specialization of the absorbed low-frequency theorem. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_primeFourierMode_zero_sub_integral_Ico_le_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving) (S : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop,
      ∀ (a b : ℕ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) ((0, 0) : ℤ × ℤ) N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ))
          ((0, 0) : ℤ × ℤ) N M 2‖ ≤
          P / (Real.log P) ^ S := by
  obtain ⟨C, hC, hmode⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le_logSaving 0 S
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmode] with P hmodeP
  intro a b N M hPa hab hbP
  simpa [reciprocalPhaseScale] using
    hmodeP a b ((0, 0) : ℤ × ℤ) N M hPa hab hbP
      (by simp [reciprocalPhaseScale])

end

end Tao2026
