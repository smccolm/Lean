import RiemannZeta.GuthMaynard.HughesYoungParameterChoice

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global elementary bounds for the Hughes--Young assembly
-/

/-- Inserting one pair of nonnegative dyadic cutoffs cannot increase the
norm of the corresponding height-integrated source term. -/
theorem norm_hughesYoungFullDyadicIntegratedTerm_le
    {T c H : ℝ} {h k i j m n : ℕ}
    (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n)‖ ≤
      ‖∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n)‖ := by
  rw [hughesYoungFullDyadicIntegratedTerm_eq_source T c H hh hk,
    integral_hughesYoungFiniteArithmeticTerm_eq_source T c H hh hk]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (hughesYoungFullDyadicCutoff_nonneg_nat _ _),
    abs_of_nonneg (hughesYoungFullDyadicCutoff_nonneg_nat _ _)]
  have hleft := (hughesYoungDyadicCutoffAt_mem_Icc
    (hughesYoungFullDyadicScale_pos i) (by positivity : (0 : ℝ) ≤
      ((hughesYoungReducedLeft h k * m : ℕ) : ℝ))).2
  have hright := (hughesYoungDyadicCutoffAt_mem_Icc
    (hughesYoungFullDyadicScale_pos j) (by positivity : (0 : ℝ) ≤
      ((hughesYoungReducedRight h k * n : ℕ) : ℝ))).2
  have hleft' : hughesYoungFullDyadicCutoff i
      ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) ≤ 1 := by
    simpa only [hughesYoungFullDyadicCutoff] using hleft
  have hright' : hughesYoungFullDyadicCutoff j
      ((hughesYoungReducedRight h k * n : ℕ) : ℝ) ≤ 1 := by
    simpa only [hughesYoungFullDyadicCutoff] using hright
  have hprod : hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) *
        hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hleft' hright'
        (hughesYoungFullDyadicCutoff_nonneg_nat _ _) (by norm_num)
      _ = 1 := one_mul 1
  calc
    hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) *
        hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) *
        ‖divisorWeight m‖ * ‖divisorWeight n‖ *
          ‖hughesYoungIntegratedSourceWeight T c H h k
            ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)‖ ≤
      1 * ‖divisorWeight m‖ * ‖divisorWeight n‖ *
          ‖hughesYoungIntegratedSourceWeight T c H h k
            ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)‖ := by
              gcongr
    _ = _ := by ring

/-- The static Hughes--Young localization factor retains the two critical-line
weights exactly.  Keeping these factors is essential when the DFI central term
is summed over the mollifier variables: after gcd reduction they combine with
the DFI factor `(ab)^(-1/2)` to give the summable weight `gcd(h,k)/(hk)`. -/
theorem norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow
    {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 / Real.pi) := by
  have hlogh :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ)‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hh)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    norm_num
  have hlogk :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ)‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hk)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    norm_num
  unfold hughesYoungLocalizedStaticScalar
  simp only [norm_mul, hlogh, hlogk, norm_div, norm_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Exact arithmetic simplification after Hughes--Young gcd reduction.  The
two critical-line weights and DFI's reduced-coefficient square-root factor
collapse to `gcd(h,k)/(hk)`. -/
theorem hughesYoung_criticalWeights_mul_reduced_rpow_eq_gcd_div
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
          (-(1 / 2 : ℝ))) =
      (hughesYoungCommonDivisor h k : ℝ) / ((h : ℝ) * (k : ℝ)) := by
  let d := hughesYoungCommonDivisor h k
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have hd : 0 < d := hughesYoungCommonDivisor_pos hh
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hha : d * a = h := hughesYoungCommonDivisor_mul_reducedLeft h k
  have hkb : d * b = k := hughesYoungCommonDivisor_mul_reducedRight h k
  change (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
      ((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (d : ℝ) / ((h : ℝ) * (k : ℝ))
  rw [← hha, ← hkb]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg a),
    Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg b),
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.rpow_neg (Nat.cast_nonneg d), Real.rpow_neg (Nat.cast_nonneg a),
    Real.rpow_neg (Nat.cast_nonneg b)]
  have hdsqrt : (d : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt d := by
    rw [Real.sqrt_eq_rpow]
  have hasqrt : (a : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt a := by
    rw [Real.sqrt_eq_rpow]
  have hbsqrt : (b : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
  rw [hdsqrt, hasqrt, hbsqrt]
  field_simp [ne_of_gt hdR, ne_of_gt haR, ne_of_gt hbR,
    ne_of_gt (Real.sqrt_pos.2 hdR), ne_of_gt (Real.sqrt_pos.2 haR),
    ne_of_gt (Real.sqrt_pos.2 hbR)]
  rw [Real.sq_sqrt (Nat.cast_nonneg d),
    Real.sq_sqrt (Nat.cast_nonneg a),
    Real.sq_sqrt (Nat.cast_nonneg b)]

/-- Exact combination of the localized coefficient factor with the reduced
DFI square-root factor. -/
theorem norm_hughesYoungLocalizedStaticScalar_mul_reduced_rpow_eq
    {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
          (-(1 / 2 : ℝ))) =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) * (1 / Real.pi) := by
  rw [norm_hughesYoungLocalizedStaticScalar_eq_coefficients_mul_rpow hh hk]
  rw [show Nat.gcd h k = hughesYoungCommonDivisor h k by rfl]
  rw [← hughesYoung_criticalWeights_mul_reduced_rpow_eq_gcd_div hh hk]
  ring

/-- The `Icc 1 L` form of the harmonic gcd average proved in the DFI
arithmetic layer. -/
theorem sum_Icc_gcd_div_le_harmonic
    (L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Icc 1 L, (Nat.gcd H q : ℝ) / q) ≤
      (H.divisors.card : ℝ) * (((harmonic (L + 1) : ℚ) : ℝ)) := by
  have hset : Finset.Ioo 0 (L + 1) = Finset.Icc 1 L := by
    ext q
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [← hset]
  exact sum_Ioo_gcd_div_le 0 (L + 1) H hH

/-- A reusable finite double-sum estimate for the exact gcd weight arising
from the Hughes--Young/DFI reduction. -/
theorem weightedGCDMass_le
    (c : ℕ → ℂ) (L : ℕ) {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : ∀ n ∈ Finset.Icc 1 L, ‖c n‖ ≤ B)
    (hdiv : ∀ n ∈ Finset.Icc 1 L, (n.divisors.card : ℝ) ≤ E) :
    (∑ h ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
      B ^ 2 * E * (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
  let H : ℝ := (((harmonic (L + 1) : ℚ) : ℝ))
  have hH : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hinner : ∀ h ∈ Finset.Icc 1 L,
      (∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
        (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) := by
    intro h hh
    have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
    calc
      (∑ k ∈ Finset.Icc 1 L,
          ‖c h‖ * ‖c k‖ *
            ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
        ∑ k ∈ Finset.Icc 1 L,
          (B ^ 2 / (h : ℝ)) * ((Nat.gcd h k : ℝ) / (k : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk0 : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
            have hcprod : ‖c h‖ * ‖c k‖ ≤ B ^ 2 := by
              calc
                ‖c h‖ * ‖c k‖ ≤ B * B :=
                  mul_le_mul (hc h hh) (hc k hk) (norm_nonneg _) hB
                _ = B ^ 2 := by ring
            calc
              ‖c h‖ * ‖c k‖ *
                    ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) ≤
                  B ^ 2 *
                    ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) := by
                      gcongr
              _ = (B ^ 2 / (h : ℝ)) *
                    ((Nat.gcd h k : ℝ) / (k : ℝ)) := by
                      field_simp
      _ = (B ^ 2 / (h : ℝ)) *
          (∑ k ∈ Finset.Icc 1 L, (Nat.gcd h k : ℝ) / (k : ℝ)) := by
            rw [Finset.mul_sum]
      _ ≤ (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) := by
            gcongr
            exact sum_Icc_gcd_div_le_harmonic L h hh0.ne'
  calc
    (∑ h ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
      ∑ h ∈ Finset.Icc 1 L,
        (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) :=
          Finset.sum_le_sum hinner
    _ ≤ ∑ h ∈ Finset.Icc 1 L,
        (B ^ 2 / (h : ℝ)) * (E * H) := by
          apply Finset.sum_le_sum
          intro h hh
          gcongr
          exact hdiv h hh
    _ = (B ^ 2 * E * H) *
        (∑ h ∈ Finset.Icc 1 L, (h : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [div_eq_mul_inv]
          ring
    _ = (B ^ 2 * E * H) * (((harmonic L : ℚ) : ℝ)) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rfl
    _ ≤ (B ^ 2 * E * H) * H := by
          gcongr
          dsimp only [H]
          rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
          push_cast
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          · intro n _hn _hnL
            positivity
    _ = B ^ 2 * E * (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
          dsimp only [H]
          ring

/-- The exact mollifier-weighted gcd mass occurring in the unshifted
Hughes--Young central term. -/
noncomputable def hughesYoungMollifierWeightedGCDMass (T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))

/-- The exact weighted gcd mass has only epsilon-power and harmonic losses;
in particular, it has no fixed power loss from the mollifier length. -/
theorem exists_hughesYoungMollifierWeightedGCDMass_le
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ {T : ℝ},
      hughesYoungMollifierWeightedGCDMass T ≤
        (A * (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ δ) ^ 2 *
          (D * (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ δ) *
          (((harmonic ((detectorCutoff T) ^ 2 + 1) : ℚ) : ℝ)) ^ 2 := by
  obtain ⟨A, hA, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  obtain ⟨D, hD, hdiv⟩ := divisorCountBound_native δ hδ
  refine ⟨A, D, hA, hD, ?_⟩
  intro T
  let L := (detectorCutoff T) ^ 2
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hcoeffL : ∀ n ∈ Finset.Icc 1 L,
      ‖shortMobiusSquareCoeff T n‖ ≤ A * (L : ℝ) ^ δ := by
    intro n hn
    have hn0 : 0 < n := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
    calc
      ‖shortMobiusSquareCoeff T n‖ ≤ A * (n : ℝ) ^ δ := hcoeff T n hn0
      _ ≤ A * (L : ℝ) ^ δ := by
        gcongr
        exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hdivL : ∀ n ∈ Finset.Icc 1 L,
      (n.divisors.card : ℝ) ≤ D * (L : ℝ) ^ δ := by
    intro n hn
    have hn0 : 0 < n := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
    calc
      (n.divisors.card : ℝ) ≤ D * (n : ℝ) ^ δ := hdiv n hn0
      _ ≤ D * (L : ℝ) ^ δ := by
        gcongr
        exact_mod_cast (Finset.mem_Icc.mp hn).2
  change (∑ h ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤ _
  exact weightedGCDMass_le (shortMobiusSquareCoeff T) L
    (mul_nonneg hA.le (Real.rpow_nonneg hL0 δ))
    (mul_nonneg hD.le (Real.rpow_nonneg hL0 δ)) hcoeffL hdivL

theorem hughesYoungMollifierWeightedGCDMass_nonneg (T : ℝ) :
    0 ≤ hughesYoungMollifierWeightedGCDMass T := by
  unfold hughesYoungMollifierWeightedGCDMass
  positivity

/-- The mollifier-weighted gcd mass is subpolynomial in the physical height.
This is the global arithmetic summation needed by the Hughes--Young consumer. -/
theorem hughesYoungMollifierWeightedGCDMass_epsilonPowerBound :
    EpsilonPowerBound hughesYoungMollifierWeightedGCDMass (fun _ => 1) := by
  intro ε hε
  let δ : ℝ := ε / 10
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨A, D, hA, hD, hmass⟩ :=
    exists_hughesYoungMollifierWeightedGCDMass_le δ hδ
  let C : ℝ := A ^ 2 * D * (1 + δ⁻¹) ^ 2 * (2 : ℝ) ^ (2 * δ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  apply IsBigO.of_bound C
  filter_upwards [eventually_detectorCutoff_sq_le_rpow,
      eventually_ge_atTop (1 : ℝ)] with T hcut hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let L : ℕ := (detectorCutoff T) ^ 2
  have hL : (L : ℝ) ≤ T := by
    calc
      (L : ℝ) ≤ T ^ (1 / 22 : ℝ) := by
        simpa only [L, Nat.cast_pow] using hcut
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := Real.rpow_one T
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hLone : (1 : ℝ) ≤ (L + 1 : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hLsucc : ((L + 1 : ℕ) : ℝ) ≤ 2 * T := by
    push_cast
    linarith
  have hpowL : (L : ℝ) ^ δ ≤ T ^ δ :=
    Real.rpow_le_rpow hL0 hL hδ.le
  have hpowSucc : ((L + 1 : ℕ) : ℝ) ^ δ ≤ (2 * T) ^ δ :=
    Real.rpow_le_rpow (by positivity) hLsucc hδ.le
  have hH := harmonic_le_epsilon_rpow hδ (L + 1)
  have hmax : max 1 (((L + 1 : ℕ) : ℝ) ^ δ) =
      ((L + 1 : ℕ) : ℝ) ^ δ := max_eq_right <|
        Real.one_le_rpow hLone hδ.le
  rw [hmax] at hH
  have hHbound : (((harmonic (L + 1) : ℚ) : ℝ)) ≤
      (1 + δ⁻¹) * (2 * T) ^ δ :=
    hH.trans (mul_le_mul_of_nonneg_left hpowSucc (by positivity))
  have hmass' := hmass (T := T)
  change hughesYoungMollifierWeightedGCDMass T ≤
      (A * (L : ℝ) ^ δ) ^ 2 * (D * (L : ℝ) ^ δ) *
        (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 at hmass'
  have hH0 : 0 ≤ (((harmonic (L + 1) : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hraw : hughesYoungMollifierWeightedGCDMass T ≤
      (A * T ^ δ) ^ 2 * (D * T ^ δ) *
        (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 := by
    calc
      _ ≤ (A * (L : ℝ) ^ δ) ^ 2 * (D * (L : ℝ) ^ δ) *
          (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := hmass'
      _ ≤ (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
        gcongr
      _ ≤ (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 := by
        gcongr
  have hpowTwo : (2 * T) ^ δ = (2 : ℝ) ^ δ * T ^ δ := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
  have hcombine :
      (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 =
        C * T ^ (5 * δ) := by
    rw [hpowTwo]
    have hp : (T ^ δ) ^ 2 = T ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      ring_nf
    have hp2 : ((2 : ℝ) ^ δ) ^ 2 = (2 : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    rw [mul_pow, mul_pow, mul_pow, hp, hp2]
    dsimp only [C]
    rw [show T ^ (5 * δ) = T ^ (2 * δ) * T ^ δ * T ^ (2 * δ) by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 1
      ring]
    ring
  have hexp : 5 * δ = ε / 2 := by dsimp only [δ]; ring
  have hpowFinal : T ^ (5 * δ) ≤ T ^ ε := by
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  simp only [Real.norm_eq_abs, abs_abs, abs_one, mul_one]
  rw [abs_of_nonneg (hughesYoungMollifierWeightedGCDMass_nonneg T),
    abs_of_nonneg (Real.rpow_nonneg hT0.le ε)]
  exact hraw.trans_eq hcombine |>.trans
    (mul_le_mul_of_nonneg_left hpowFinal hC)

/-- A direct finite bound for the exact `ℓ¹` mass of the squared short
Möbius coefficients. -/
theorem detectorCutoff_le_three_mul_rpow_one_hundredth
    {T : ℝ} (hT : 1 ≤ T) :
    (detectorCutoff T : ℝ) ≤ 3 * T ^ (1 / 100 : ℝ) := by
  have hpow0 : 0 ≤ T ^ (1 / 100 : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hT) _
  rw [detectorCutoff]
  push_cast
  calc
    (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) + 1 ≤
        2 * T ^ (1 / 100 : ℝ) + 1 := by
      gcongr
      exact Nat.floor_le (by positivity)
    _ ≤ 3 * T ^ (1 / 100 : ℝ) := by
      have hpone : 1 ≤ T ^ (1 / 100 : ℝ) :=
        Real.one_le_rpow hT (by norm_num)
      linarith

theorem one_half_le_hughesYoungFullDyadicScale (i : ℕ) :
    (1 / 2 : ℝ) ≤ hughesYoungFullDyadicScale i := by
  cases i with
  | zero =>
      simp only [hughesYoungFullDyadicScale]
      have hr := hughesYoungDyadicRatio_lt_two
      have hr0 := hughesYoungDyadicRatio_pos
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hr0).mpr
      linarith
  | succ i =>
      simp only [hughesYoungFullDyadicScale]
      exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
        (one_le_hughesYoungDyadicScale i)

/-- Membership in the active product filter bounds either physical scale by
twice the complete source conductor. -/
theorem hughesYoungFullDyadicScale_le_two_mul_activeConductor_left
    {a b R K : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hughesYoungActiveDyadicBoxes a b R K) :
    hughesYoungFullDyadicScale ij.1 ≤ 2 * (a * b * R : ℕ) := by
  have hs := (Finset.mem_filter.mp hij).2
  have hy := one_half_le_hughesYoungFullDyadicScale ij.2
  have hx := hughesYoungFullDyadicScale_pos ij.1
  nlinarith

theorem hughesYoungFullDyadicScale_le_two_mul_activeConductor_right
    {a b R K : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hughesYoungActiveDyadicBoxes a b R K) :
    hughesYoungFullDyadicScale ij.2 ≤ 2 * (a * b * R : ℕ) := by
  have hs := (Finset.mem_filter.mp hij).2
  have hx := one_half_le_hughesYoungFullDyadicScale ij.1
  have hy := hughesYoungFullDyadicScale_pos ij.2
  nlinarith

theorem hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
    {a b R K : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hughesYoungActiveDyadicBoxes a b R K) :
    hughesYoungFullDyadicBound ij.1 ≤ 4 * (a * b * R) + 1 := by
  unfold hughesYoungFullDyadicBound
  have hs := hughesYoungFullDyadicScale_le_two_mul_activeConductor_left hij
  have hreal : 2 * hughesYoungFullDyadicScale ij.1 ≤
      (((4 * (a * b * R) : ℕ) : ℝ)) := by
    calc
      2 * hughesYoungFullDyadicScale ij.1 ≤
          2 * (2 * ((a * b * R : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = (((4 * (a * b * R) : ℕ) : ℝ)) := by
        push_cast
        ring
  have hceil : Nat.ceil (2 * hughesYoungFullDyadicScale ij.1) ≤
      Nat.ceil (((4 * (a * b * R) : ℕ) : ℝ)) := Nat.ceil_mono hreal
  rw [Nat.ceil_natCast] at hceil
  omega

theorem hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
    {a b R K : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hughesYoungActiveDyadicBoxes a b R K) :
    hughesYoungFullDyadicBound ij.2 ≤ 4 * (a * b * R) + 1 := by
  unfold hughesYoungFullDyadicBound
  have hs := hughesYoungFullDyadicScale_le_two_mul_activeConductor_right hij
  have hreal : 2 * hughesYoungFullDyadicScale ij.2 ≤
      (((4 * (a * b * R) : ℕ) : ℝ)) := by
    calc
      2 * hughesYoungFullDyadicScale ij.2 ≤
          2 * (2 * ((a * b * R : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = (((4 * (a * b * R) : ℕ) : ℝ)) := by
        push_cast
        ring
  have hceil : Nat.ceil (2 * hughesYoungFullDyadicScale ij.2) ≤
      Nat.ceil (((4 * (a * b * R) : ℕ) : ℝ)) := Nat.ceil_mono hreal
  rw [Nat.ceil_natCast] at hceil
  omega

/-- The fixed `h,k` scalar in the Hughes--Young localization is bounded by
the product of the two genuine mollifier coefficients.  The omitted factors
are exactly `h⁻¹⁄² k⁻¹⁄² /π`, hence at most one for positive indices. -/
theorem norm_hughesYoungLocalizedStaticScalar_le_coefficients
    {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ ≤
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogh :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ)‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hh)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    norm_num
  have hlogk :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ)‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hk)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    norm_num
  have hhpow : (h : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hhR (by norm_num)
  have hkpow : (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hkR (by norm_num)
  unfold hughesYoungLocalizedStaticScalar
  simp only [norm_mul, hlogh, hlogk, norm_div, norm_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hpi : 1 / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  have hprod :
      (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hhpow hkpow
        (Real.rpow_nonneg (by positivity) _) (by norm_num)
      _ = 1 := by norm_num
  have hall :
      (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / Real.pi) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hprod hpi (by positivity) (by norm_num)
      _ = 1 := by norm_num
  calc
    _ = (‖shortMobiusSquareCoeff T h‖ *
        ‖shortMobiusSquareCoeff T k‖) *
        ((h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / Real.pi)) := by ring
    _ ≤ (‖shortMobiusSquareCoeff T h‖ *
        ‖shortMobiusSquareCoeff T k‖) * 1 :=
      mul_le_mul_of_nonneg_left hall
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_one _

theorem hughesYoungMollifierCoefficientMass_le_cutoff_fourth (T : ℝ) :
    hughesYoungMollifierCoefficientMass T ≤
      ((detectorCutoff T : ℝ) ^ 4) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hterm : ∀ h ∈ S,
      ‖shortMobiusSquareCoeff T h‖ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
    intro h hh
    have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    calc
      ‖shortMobiusSquareCoeff T h‖ ≤ (h.divisors.card : ℝ) :=
        norm_shortMobiusSquareCoeff_le_divisors T hh0
      _ ≤ (h : ℝ) := by exact_mod_cast Nat.card_divisors_le_self h
      _ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
        exact_mod_cast (Finset.mem_Icc.mp hh).2
  unfold hughesYoungMollifierCoefficientMass
  change (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤ _
  calc
    (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤
        ∑ _h ∈ S, ((detectorCutoff T : ℝ) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * ((detectorCutoff T : ℝ) ^ 2) := by simp
    _ ≤ ((detectorCutoff T : ℝ) ^ 2) *
        ((detectorCutoff T : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast (show S.card ≤ (detectorCutoff T) ^ 2 by simp [S])
    _ = (detectorCutoff T : ℝ) ^ 4 := by ring

theorem hughesYoungMollifierCoefficientMass_le_height_fourth
    {T : ℝ} (hT : 1 ≤ T) :
    hughesYoungMollifierCoefficientMass T ≤ 81 * T ^ (4 : ℝ) := by
  have hcut := detectorCutoff_le_three_mul T hT
  calc
    hughesYoungMollifierCoefficientMass T ≤
        ((detectorCutoff T : ℝ) ^ 4) :=
      hughesYoungMollifierCoefficientMass_le_cutoff_fourth T
    _ ≤ (3 * T) ^ 4 := by gcongr
    _ = 81 * T ^ (4 : ℝ) := by
      simp only [Real.rpow_ofNat]
      ring

/-- The actual short-mollifier mass has only the source-scale epsilon loss.
This sharp form, unlike the elementary fourth-power estimate, is suitable
for the final Hughes--Young exponent assembly. -/
theorem exists_hughesYoungMollifierCoefficientMass_le_power
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T →
      hughesYoungMollifierCoefficientMass T ≤
        C * T ^ ((2 + 2 * δ) / 100 : ℝ) := by
  obtain ⟨A, hA, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  let C : ℝ := A * 3 ^ (2 + 2 * δ : ℝ)
  have hC : 0 < C := mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro T hT
  let Q := detectorCutoff T
  let S := Finset.Icc 1 (Q ^ 2)
  have hQpos : 0 < Q := by simp [Q, detectorCutoff]
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hterm : ∀ h ∈ S, ‖shortMobiusSquareCoeff T h‖ ≤
      A * ((Q : ℝ) ^ 2) ^ δ := by
    intro h hh
    have hhpos : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    have hhQ : (h : ℝ) ≤ (Q : ℝ) ^ 2 := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact (hcoeff T h hhpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hhQ hδ.le) hA.le)
  have hcard : (S.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast (show S.card ≤ Q ^ 2 by simp [S])
  have hsum : hughesYoungMollifierCoefficientMass T ≤
      ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) := by
    unfold hughesYoungMollifierCoefficientMass
    change (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤ _
    calc
      _ ≤ ∑ _h ∈ S, A * ((Q : ℝ) ^ 2) ^ δ := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (A * ((Q : ℝ) ^ 2) ^ δ) := by simp
      _ ≤ ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) := by gcongr
  have hpower : ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) =
      A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := by
    rw [show (Q : ℝ) ^ 2 = (Q : ℝ) ^ (2 : ℝ) by
      exact (Real.rpow_natCast (Q : ℝ) 2).symm]
    rw [← Real.rpow_mul hQreal.le]
    calc
      _ = A * ((Q : ℝ) ^ (2 : ℝ) * (Q : ℝ) ^ (2 * δ : ℝ)) := by ring
      _ = A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := by
        rw [← Real.rpow_add hQreal]
  have hQbound : (Q : ℝ) ≤ 3 * T ^ (1 / 100 : ℝ) :=
    detectorCutoff_le_three_mul_rpow_one_hundredth hT
  calc
    hughesYoungMollifierCoefficientMass T ≤
        A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := hsum.trans_eq hpower
    _ ≤ A * (3 * T ^ (1 / 100 : ℝ)) ^ (2 + 2 * δ : ℝ) := by
      gcongr
    _ = C * T ^ ((2 + 2 * δ) / 100 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (Real.rpow_nonneg (zero_le_one.trans hT) _)]
      rw [← Real.rpow_mul (zero_le_one.trans hT)]
      dsimp [C]
      rw [show (1 / 100 : ℝ) * (2 + 2 * δ) = (2 + 2 * δ) / 100 by ring]
      ring

set_option maxRecDepth 10000 in
/-- With the global radius and depth, the sum of all omitted dyadic boxes in the
Hughes--Young active decomposition is `O(T)`.  The deliberately excessive radius
`T^5` absorbs the polynomial losses in the pointwise Mellin-tail estimate. -/
theorem exists_norm_hughesYoungGlobalOpeningRemainder_le_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ‖hughesYoungActiveWholeSmoothedRemainder 100 T
          (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖ ≤ C * T := by
  obtain ⟨L, hL, hrem⟩ :=
    exists_norm_hughesYoungActiveWholeSmoothedRemainder_le
      100 (by norm_num) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let C : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) *
      (256 * Real.exp (400 * (100 : ℝ) ^ 2) *
        207 ^ (408 : ℕ) *
        (hughesYoungReferenceDivisorPairMass (1 / 2) + 1) * L)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (by positivity))
      (mul_pos
        (mul_pos (mul_pos (by positivity) (by positivity))
          (by linarith [hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)])) hL)
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR := hughesYoungGlobalRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungGlobalRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungGlobal_cover (by linarith [Real.exp_one_gt_d9]) hh hk
  have hraw := hrem hT hR hcover
  have hraw' :
      ‖hughesYoungActiveWholeSmoothedRemainder 100 T
          (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
            ((207 : ℝ) * T) ^ (408 : ℕ) *
            (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) := by
    convert hraw using 1
    all_goals norm_num
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hpair0 := hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)
  have hpair : hughesYoungReferenceDivisorPairMass (1 / 2) ≤
      hughesYoungReferenceDivisorPairMass (1 / 2) + 1 := by linarith
  have hrneg : (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) ≤
      T ^ (-995 : ℝ) := by
    have hlower : T ^ (5 : ℝ) ≤ (hughesYoungGlobalRadius T : ℝ) :=
      Nat.le_ceil _
    have hneg := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hT0 (5 : ℝ)) hlower
        (by norm_num : (-199 : ℝ) ≤ 0)
    calc
      _ ≤ (T ^ (5 : ℝ)) ^ (-199 : ℝ) := hneg
      _ = T ^ (-995 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
  have hbound :
      (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
            ((207 : ℝ) * T) ^ (408 : ℕ) *
            (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) ≤
        C * (T ^ (-578 : ℝ)) := by
    calc
      _ ≤
          (15 * T / 4) * (81 * T ^ (4 : ℝ)) ^ 2 *
            (1 / Real.pi) *
            ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
              ((207 : ℝ) * T) ^ (408 : ℕ) *
              T ^ (-995 : ℝ) *
              (hughesYoungReferenceDivisorPairMass (1 / 2) + 1)) * L) := by
        gcongr
      _ = C * T ^ (-578 : ℝ) := by
        have hfour : (T ^ (4 : ℝ)) ^ 2 = T ^ (8 : ℝ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          norm_num
        have hpowers :
            T * T ^ (8 : ℝ) * T ^ (408 : ℕ) * T ^ (-995 : ℝ) =
              T ^ (-578 : ℝ) := by
          calc
            _ = T ^ (1 : ℝ) * T ^ (8 : ℝ) * T ^ (408 : ℝ) *
                T ^ (-995 : ℝ) := by
              rw [Real.rpow_one]
              exact congrArg
                (fun x : ℝ => T * T ^ (8 : ℝ) * x * T ^ (-995 : ℝ))
                (Real.rpow_natCast T 408).symm
            _ = T ^ ((1 : ℝ) + 8) * T ^ (408 : ℝ) * T ^ (-995 : ℝ) := by
              rw [← Real.rpow_add hT0]
            _ = T ^ ((1 : ℝ) + 8 + 408) * T ^ (-995 : ℝ) := by
              rw [← Real.rpow_add hT0]
            _ = T ^ ((1 : ℝ) + 8 + 408 - 995) := by
              rw [← Real.rpow_add hT0]
              norm_num
            _ = T ^ (-578 : ℝ) := by norm_num
        rw [mul_pow, hfour]
        calc
          _ = C *
              (T * T ^ (8 : ℝ) * T ^ (408 : ℕ) * T ^ (-995 : ℝ)) := by
            dsimp only [C]
            set_option exponentiation.threshold 512 in ring
          _ = C * T ^ (-578 : ℝ) := by rw [hpowers]
  have hlast : C * T ^ (-578 : ℝ) ≤ C * T := by
    have hp : T ^ (-578 : ℝ) ≤ T := by
      calc
        T ^ (-578 : ℝ) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := by simp
    exact mul_le_mul_of_nonneg_left hp hC.le
  exact hraw'.trans (hbound.trans hlast)

end RiemannZeta.GuthMaynard
