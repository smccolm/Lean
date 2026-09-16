import Tao2026.MangoldtSourceBlock
import Tao2026.PartialSummation

/-!
# Prime transfer for the canonical quadratic source block

This module passes from the quantitative Mangoldt reciprocal-phase estimate
to logarithmically weighted and then unweighted prime sums.  Endpoint
conversion to the frozen local prime-power estimate is kept exact.
-/

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The half-open natural interval `[a,b)` is the local-cover interval
`(a-1,a-1+(b-a)]` when `a≤b` and `a>0`. -/
theorem Ico_eq_Ioc_floor_sub_one
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Finset.Ico a b =
      Finset.Ioc ⌊(a : ℝ) - 1⌋₊
        ⌊((a : ℝ) - 1) + ((b - a : ℕ) : ℝ)⌋₊ := by
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  have hafloor : ⌊(a : ℝ) - 1⌋₊ = a - 1 := by
    have haone : 1 ≤ a := by omega
    have hacast : (((a - 1 : ℕ) : ℕ) : ℝ) = (a : ℝ) - 1 := by
      norm_num [Nat.cast_sub haone]
    rw [← hacast]
    simp
  have htop : ((a : ℝ) - 1) + ((b - a : ℕ) : ℝ) = (b : ℝ) - 1 := by
    push_cast [Nat.cast_sub hab]
    ring
  have hbfloor : ⌊(b : ℝ) - 1⌋₊ = b - 1 := by
    by_cases hb : b = 0
    · omega
    · have hbone : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
      have hbcast : (((b - 1 : ℕ) : ℕ) : ℝ) = (b : ℝ) - 1 := by
        norm_num [Nat.cast_sub hbone]
      rw [← hbcast]
      simp
  rw [hafloor, htop, hbfloor]
  omega

/-- Exact identification of the higher-prime-power tail on `[a,b)` with the
frozen local interval convention. -/
theorem primePowerTailReciprocalPhaseSum_Ico_eq_interval
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (N M : ℝ) (j : ℕ) :
    primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j =
      intervalPrimePowerTailReciprocalPhaseSum
        ((a : ℝ) - 1) ((b - a : ℕ) : ℝ) N M j := by
  unfold intervalPrimePowerTailReciprocalPhaseSum
  rw [← Ico_eq_Ioc_floor_sub_one ha hab]

/-- Explicit higher-prime-power bound on the same half-open interval used by
the Vaughan and Abel layers. -/
theorem norm_primePowerTailReciprocalPhaseSum_Ico_le_explicit
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (N M : ℝ) (j : ℕ) :
    ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
      (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) / Real.log 2⌋₊ : ℝ) *
        (((((a : ℝ) - 1) ^ (-(1 / 2 : ℝ))) * (b - a : ℕ) + 1) *
          Real.log (((a : ℝ) - 1) + (b - a : ℕ))) := by
  rw [primePowerTailReciprocalPhaseSum_Ico_eq_interval (by omega) hab]
  apply norm_intervalPrimePowerTailReciprocalPhaseSum_le_explicit
  · have haReal : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  · positivity

/-- Removing higher prime powers from a Mangoldt phase estimate costs exactly
the norm of the local tail. -/
theorem norm_primeLogReciprocalPhaseSum_Ico_le_mangoldt_add_tail
    (a b : ℕ) (N M : ℝ) (j : ℕ) :
    ‖primeLogReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
      ‖mangoldtReciprocalPhaseSum N M j a b‖ +
        ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ := by
  have hsplit := weightedMangoldtSum_eq_primeLog_add_primePowerTail
    (Finset.Ico a b) N M j
  change mangoldtReciprocalPhaseSum N M j a b = _ at hsplit
  have hrepr : primeLogReciprocalPhaseSum (Finset.Ico a b) N M j =
      mangoldtReciprocalPhaseSum N M j a b -
        primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j := by
    rw [hsplit]
    ring
  rw [hrepr]
  exact norm_sub_le _ _

/-- Fully explicit finite Mangoldt-to-prime-log transfer on a half-open
interval. -/
theorem norm_primeLogReciprocalPhaseSum_Ico_le_mangoldt_add_explicit
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (N M : ℝ) (j : ℕ) :
    ‖primeLogReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
      ‖mangoldtReciprocalPhaseSum N M j a b‖ +
      (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) / Real.log 2⌋₊ : ℝ) *
        (((((a : ℝ) - 1) ^ (-(1 / 2 : ℝ))) * (b - a : ℕ) + 1) *
          Real.log (((a : ℝ) - 1) + (b - a : ℕ))) := by
  exact (norm_primeLogReciprocalPhaseSum_Ico_le_mangoldt_add_tail
    a b N M j).trans (add_le_add le_rfl
      (norm_primePowerTailReciprocalPhaseSum_Ico_le_explicit
        ha hab N M j))

/-- Uniform dyadic simplification of the exact local prime-power envelope.
It retains a fixed quarter-power saving, which is more than enough for every
later logarithmic target. -/
theorem norm_primePowerTailReciprocalPhaseSum_Ico_le_dyadic
    {P a b : ℕ} (hP : 16 ≤ P) (hPa : P ≤ a) (hab : a ≤ b)
    (hbP : b ≤ 2 * P) (N M : ℝ) (j : ℕ) :
    ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
      4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
        (Real.log (2 * P)) ^ 2 := by
  have ha : 2 ≤ a := by omega
  have hraw := norm_primePowerTailReciprocalPhaseSum_Ico_le_explicit
    ha hab N M j
  have hPpos : (0 : ℝ) < P := by positivity
  have haReal : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hxpos : 0 < (a : ℝ) - 1 := by linarith
  have htOne : 1 ≤ ((a : ℝ) - 1) + (b - a : ℕ) := by
    have hy0 : (0 : ℝ) ≤ (b - a : ℕ) := by positivity
    linarith
  have htpos : 0 < ((a : ℝ) - 1) + (b - a : ℕ) :=
    zero_lt_one.trans_le htOne
  have htEq : ((a : ℝ) - 1) + (b - a : ℕ) = (b : ℝ) - 1 := by
    push_cast [Nat.cast_sub hab]
    ring
  have htTop : ((a : ℝ) - 1) + (b - a : ℕ) ≤ 2 * P := by
    rw [htEq]
    have hbPReal : (b : ℝ) ≤ 2 * P := by exact_mod_cast hbP
    linarith
  have hlogt0 : 0 ≤ Real.log (((a : ℝ) - 1) + (b - a : ℕ)) :=
    Real.log_nonneg htOne
  have hlogTopPos : 0 < Real.log (2 * P) := by
    apply Real.log_pos
    have hPReal : (16 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hlogle : Real.log (((a : ℝ) - 1) + (b - a : ℕ)) ≤
      Real.log (2 * P) := Real.log_le_log htpos htTop
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfactor : (1 : ℝ) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hratio0 : 0 ≤
      Real.log (((a : ℝ) - 1) + (b - a : ℕ)) / Real.log 2 :=
    div_nonneg hlogt0 hlogTwo.le
  have hfloor :
      (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) /
          Real.log 2⌋₊ : ℝ) ≤ 2 * Real.log (2 * P) := by
    calc
      (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) /
          Real.log 2⌋₊ : ℝ) ≤
          Real.log (((a : ℝ) - 1) + (b - a : ℕ)) /
            Real.log 2 := Nat.floor_le hratio0
      _ ≤ 2 * Real.log (((a : ℝ) - 1) + (b - a : ℕ)) := by
        apply (div_le_iff₀ hlogTwo).2
        nlinarith [mul_le_mul_of_nonneg_left hfactor hlogt0]
      _ ≤ 2 * Real.log (2 * P) := by linarith
  have hsqrt : Real.sqrt (P : ℝ) ≤ (a : ℝ) - 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · have hPaReal : (P : ℝ) ≤ a := by exact_mod_cast hPa
      have hPReal : (16 : ℝ) ≤ P := by exact_mod_cast hP
      nlinarith
  have hroot : (P : ℝ) ^ (1 / 2 : ℝ) ≤ (a : ℝ) - 1 := by
    simpa only [← Real.sqrt_eq_rpow] using hsqrt
  have hinv : ((a : ℝ) - 1) ^ (-(1 / 2 : ℝ)) ≤
      (P : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hmono := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hPpos (1 / 2 : ℝ)) hroot
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    calc
      ((a : ℝ) - 1) ^ (-(1 / 2 : ℝ)) ≤
          ((P : ℝ) ^ (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) := hmono
      _ = (P : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_mul hPpos.le]
        norm_num
  have hy : ((b - a : ℕ) : ℝ) ≤ P := by exact_mod_cast (show b - a ≤ P by omega)
  have hmiddle :
      ((a : ℝ) - 1) ^ (-(1 / 2 : ℝ)) * (b - a : ℕ) + 1 ≤
        (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1 := by
    have := mul_le_mul hinv hy (by positivity) (by positivity)
    nlinarith
  calc
    ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
        (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) / Real.log 2⌋₊ : ℝ) *
          (((((a : ℝ) - 1) ^ (-(1 / 2 : ℝ))) * (b - a : ℕ) + 1) *
            Real.log (((a : ℝ) - 1) + (b - a : ℕ))) := hraw
    _ ≤ 4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
          (Real.log (2 * P)) ^ 2 := by
      have hmid0 : 0 ≤
          (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1 := by positivity
      have hlog0 : 0 ≤ Real.log (2 * P) := hlogTopPos.le
      calc
        (⌊Real.log (((a : ℝ) - 1) + (b - a : ℕ)) / Real.log 2⌋₊ : ℝ) *
            (((((a : ℝ) - 1) ^ (-(1 / 2 : ℝ))) * (b - a : ℕ) + 1) *
              Real.log (((a : ℝ) - 1) + (b - a : ℕ))) ≤
            (2 * Real.log (2 * P)) *
              (((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
                Real.log (2 * P)) := by gcongr
        _ ≤ 4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
              (Real.log (2 * P)) ^ 2 := by
          nlinarith

/-- The dyadic higher-prime-power tail is smaller than any prescribed
logarithmic fraction of the source scale. -/
theorem eventually_norm_primePowerTailReciprocalPhaseSum_Ico_le_logSaving
    (T : ℝ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N M : ℝ) (j : ℕ),
      P ≤ a → a ≤ b → b ≤ 2 * P →
      ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
        (P : ℝ) * (Real.log P) ^ (-T) := by
  have habsorbReal := eventually_rpow_neg_le_log_rpow_neg
    (c := (1 / 4 : ℝ)) (by norm_num) (T + 3)
  have habsorb : ∀ᶠ P : ℕ in atTop,
      (P : ℝ) ^ (-(1 / 4 : ℝ)) ≤
        (Real.log P) ^ (-(T + 3)) :=
    tendsto_natCast_atTop_atTop.eventually habsorbReal
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 32 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 32)
  filter_upwards [habsorb, hlogLarge, eventually_ge_atTop (16 : ℕ)]
    with P habsorbP hlogP hP
  intro a b N M j hPa hab hbP
  have hraw := norm_primePowerTailReciprocalPhaseSum_Ico_le_dyadic
    hP hPa hab hbP N M j
  have hPpos : (0 : ℝ) < P := by positivity
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hlogpos : 0 < Real.log P := by linarith
  have hlogTwoLe : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ P by omega))
  have hlogTwoP : Real.log (2 * P) ≤ 2 * Real.log P := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
    linarith
  have hlogTwoPpos : 0 < Real.log (2 * P) := by
    apply Real.log_pos
    have hPReal : (16 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hprodOne : (1 : ℝ) ≤
      (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hpow : (1 : ℝ) ≤ (P : ℝ) ^ (3 / 4 : ℝ) :=
      Real.one_le_rpow hPone (by norm_num)
    calc
      (1 : ℝ) ≤ (P : ℝ) ^ (3 / 4 : ℝ) := hpow
      _ = (P : ℝ) ^ ((1 : ℝ) + (-(1 / 4 : ℝ))) := by norm_num
      _ = (P : ℝ) ^ (1 : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_add hPpos 1 (-(1 / 4 : ℝ))
      _ = (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
  have hlogSquare : (Real.log (2 * P)) ^ 2 ≤
      4 * (Real.log P) ^ 2 := by
    have hsquare := pow_le_pow_left₀ (le_of_lt hlogTwoPpos) hlogTwoP 2
    nlinarith
  have henvelope :
      4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
          (Real.log (2 * P)) ^ 2 ≤
        32 * (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) *
          (Real.log P) ^ 2 := by
    have hprod0 : 0 ≤ (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
    have hlogSq0 : 0 ≤ (Real.log (2 * P)) ^ 2 := sq_nonneg _
    calc
      4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
          (Real.log (2 * P)) ^ 2 ≤
          8 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ))) *
            (Real.log (2 * P)) ^ 2 := by nlinarith
      _ ≤ 8 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ))) *
            (4 * (Real.log P) ^ 2) := by gcongr
      _ = 32 * (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) *
            (Real.log P) ^ 2 := by ring
  have hlogIdentity :
      (Real.log P) ^ (-(T + 3)) * (Real.log P) ^ (2 : ℕ) =
        (Real.log P) ^ (-(T + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlogpos]
    congr 1
    ring
  have hlast : 32 * (Real.log P) ^ (-(T + 1)) ≤
      (Real.log P) ^ (-T) := by
    calc
      32 * (Real.log P) ^ (-(T + 1)) ≤
          Real.log P * (Real.log P) ^ (-(T + 1)) := by
        exact mul_le_mul_of_nonneg_right hlogP
          (Real.rpow_nonneg hlogpos.le _)
      _ = (Real.log P) ^ (1 : ℝ) *
          (Real.log P) ^ (-(T + 1)) := by rw [Real.rpow_one]
      _ = (Real.log P) ^ ((1 : ℝ) + (-(T + 1))) :=
        (Real.rpow_add hlogpos 1 (-(T + 1))).symm
      _ = (Real.log P) ^ (-T) := by
        congr 1
        ring
  calc
    ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
        4 * ((P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) + 1) *
          (Real.log (2 * P)) ^ 2 := hraw
    _ ≤ 32 * (P : ℝ) * (P : ℝ) ^ (-(1 / 4 : ℝ)) *
          (Real.log P) ^ 2 := henvelope
    _ ≤ 32 * (P : ℝ) * (Real.log P) ^ (-(T + 3)) *
          (Real.log P) ^ 2 := by gcongr
    _ = 32 * (P : ℝ) *
          ((Real.log P) ^ (-(T + 3)) * (Real.log P) ^ (2 : ℕ)) := by
      rw [mul_assoc]
    _ = 32 * (P : ℝ) * (Real.log P) ^ (-(T + 1)) := by
      rw [hlogIdentity]
    _ = (P : ℝ) * (32 * (Real.log P) ^ (-(T + 1))) := by
      rw [mul_comm 32 (P : ℝ), mul_assoc]
    _ ≤ (P : ℝ) * (Real.log P) ^ (-T) := by gcongr

/-- Absolute coefficient in the final quadratic prime exponential-sum
estimate. -/
noncomputable def vaughanPrimeQuadraticDecayConstant : ℝ :=
  vaughanMangoldtQuadraticDecayConstant + 1

theorem vaughanPrimeQuadraticDecayConstant_pos :
    0 < vaughanPrimeQuadraticDecayConstant := by
  unfold vaughanPrimeQuadraticDecayConstant
  linarith [vaughanMangoldtQuadraticDecayConstant_pos]

/-- High-frequency quadratic prime reciprocal-phase estimate.  The single
source range is transported uniformly to every initial prefix, higher prime
powers are absorbed, and reverse Abel summation removes the logarithmic prime
weight. -/
theorem eventually_norm_primeReciprocalPhaseSum_le_sourceRange
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P → N ≠ 0 →
      2 * (b : ℝ) *
          (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ |N| →
      |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeReciprocalPhaseSum a b N N 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-S) := by
  have hSone : 0 ≤ S + 1 := by linarith
  have hMangoldt :=
    eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange
      hVinogradov hA₀ hε haexp hSone
  obtain ⟨K, hK⟩ := eventually_atTop.1 hMangoldt
  have htail :=
    eventually_norm_primePowerTailReciprocalPhaseSum_Ico_le_logSaving (S + 1)
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [htail, hlogLarge, eventually_ge_atTop K] with
      P htailP hlogP hPK
  intro a b N hPa hab hbP hN hlower hupper
  have hPpos : 0 < P := by
    by_contra h
    have : P = 0 := Nat.eq_zero_of_not_pos h
    subst P
    norm_num at hlogP
  have haTwo : 2 ≤ a := by
    have hPgt : 2 < P := by
      by_contra h
      have hPle : P ≤ 2 := Nat.le_of_not_gt h
      have hlogle : Real.log P ≤ Real.log 2 := by
        exact Real.log_le_log (by exact_mod_cast hPpos) (by exact_mod_cast hPle)
      nlinarith [Real.log_two_lt_d9]
    omega
  have hPB : P ≤ b := hPa.trans hab.le
  have hPRealPos : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hlogPpos : 0 < Real.log P := by linarith
  have hphaseExp : 0 ≤ vaughanTypeIILogSavingPhaseExponent (S + 1) := by
    unfold vaughanTypeIILogSavingPhaseExponent
    linarith
  have hparameterExp : 0 ≤ 3 / 2 - ε := haexp
  have hpartial : ∀ k, a < k → k ≤ b →
      ‖primeLogReciprocalPhaseSum (Finset.Ico a k) N N 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-(S + 1)) := by
    intro k hak hkb
    have hPk : P ≤ k := hPa.trans hak.le
    have hkK : K ≤ k := hPK.trans hPk
    have hkP : k ≤ 2 * P := hkb.trans hbP
    have hkpos : 0 < k := hPpos.trans_le hPk
    have hlogkpos : 0 < Real.log k := by
      apply Real.log_pos
      exact_mod_cast (show 1 < k by omega)
    have hlogkb : Real.log k ≤ Real.log b := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hkb)
    have hlogPk : Real.log P ≤ Real.log k := by
      exact Real.log_le_log hPRealPos (by exact_mod_cast hPk)
    have hpowkb : (Real.log k) ^
          vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) :=
      Real.rpow_le_rpow hlogkpos.le hlogkb hphaseExp
    have hlowerk : 2 * (k : ℝ) *
          (Real.log k) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ |N| := by
      have hkbReal : (k : ℝ) ≤ b := by exact_mod_cast hkb
      calc
        2 * (k : ℝ) *
            (Real.log k) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
            2 * (b : ℝ) *
              (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) := by
          gcongr
        _ ≤ |N| := hlower
    have hupperk : |N| ≤
        A₀ * Real.exp ((Real.log k) ^ (3 / 2 - ε)) := by
      have hpowPk : (Real.log P) ^ (3 / 2 - ε) ≤
          (Real.log k) ^ (3 / 2 - ε) :=
        Real.rpow_le_rpow hlogPpos.le hlogPk hparameterExp
      calc
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) := hupper
        _ ≤ A₀ * Real.exp ((Real.log k) ^ (3 / 2 - ε)) := by gcongr
    have hMangoldtk := hK k hkK P a N hPpos hPa hak.le hkP hN hlowerk hupperk
    have hMangoldtUniform :
        ‖mangoldtReciprocalPhaseSum N N 2 a k‖ ≤
          vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) := by
      calc
        ‖mangoldtReciprocalPhaseSum N N 2 a k‖ ≤
            vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
              (Real.log k) ^ (-(S + 1)) := hMangoldtk
        _ ≤ vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
              (Real.log P) ^ (-(S + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hlogPpos hlogPk (by linarith))
            (mul_nonneg (le_of_lt vaughanMangoldtQuadraticDecayConstant_pos)
              (by positivity))
    have htailk := htailP a k N N 2 hPa hak.le hkP
    have hprimeLog := norm_primeLogReciprocalPhaseSum_Ico_le_mangoldt_add_tail
      a k N N 2
    calc
      ‖primeLogReciprocalPhaseSum (Finset.Ico a k) N N 2‖ ≤
          ‖mangoldtReciprocalPhaseSum N N 2 a k‖ +
            ‖primePowerTailReciprocalPhaseSum (Finset.Ico a k) N N 2‖ :=
        hprimeLog
      _ ≤ vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) +
          (P : ℝ) * (Real.log P) ^ (-(S + 1)) :=
        add_le_add hMangoldtUniform htailk
      _ = vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) := by
        unfold vaughanPrimeQuadraticDecayConstant
        ring
  have habel := norm_primeReciprocalPhaseSum_Ico_le
    N N 2 haTwo hab (B :=
      vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
        (Real.log P) ^ (-(S + 1))) hpartial
  have hlogPa : Real.log P ≤ Real.log a := by
    exact Real.log_le_log hPRealPos (by exact_mod_cast hPa)
  have hinv : (Real.log a)⁻¹ ≤ (Real.log P)⁻¹ :=
    inv_anti₀ hlogPpos hlogPa
  have hconstant0 : 0 ≤ vaughanPrimeQuadraticDecayConstant * (P : ℝ) := by
    exact mul_nonneg (le_of_lt vaughanPrimeQuadraticDecayConstant_pos) (by positivity)
  have hpowEq : (Real.log P) ^ (-1 : ℝ) *
      (Real.log P) ^ (-(S + 1)) = (Real.log P) ^ (-(S + 2)) := by
    rw [← Real.rpow_add hlogPpos]
    congr 1
    ring
  calc
    ‖primeReciprocalPhaseSum a b N N 2‖ ≤
        (Real.log a)⁻¹ *
          (vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1))) := habel
    _ ≤ (Real.log P)⁻¹ *
          (vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1))) := by gcongr
    _ = (vaughanPrimeQuadraticDecayConstant * (P : ℝ)) *
          ((Real.log P) ^ (-1 : ℝ) *
            (Real.log P) ^ (-(S + 1))) := by
      rw [Real.rpow_neg_one]
      ring
    _ = vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-(S + 2)) := by rw [hpowEq]
    _ ≤ vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-S) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
        hconstant0

end

end Tao2026
