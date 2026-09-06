import GafniTao.Pintz2023DetectedThreshold
import GafniTao.Pintz2023ShellExponent

/-!
# Pintz (2023), logarithmic loss ledger after equation (4.19)

The detector threshold, the two selection ceilings, the first dyadic depth,
and the bounded power are all explicit here.  One fixed logarithmic exponent
dominates them uniformly over every power allowed by equation (4.16).
-/

open Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023ShellPowerCap
    {eta target : ℝ} {k ell : ℕ}
    (data : Pintz2023PowerMarginData eta target k ell) : ℕ :=
  ⌈20 / data.epsilon⌉₊ + 1

noncomputable def pintz2023ShellLogExponent
    {eta target : ℝ} {k ell : ℕ}
    (data : Pintz2023PowerMarginData eta target k ell) : ℝ :=
  8 * (pintz2023ShellPowerCap data : ℝ) + 5

/-- The exact shell loss in the equation-(4.19) consumer is bounded by one
fixed power of `log T`, uniformly over the subsequently selected power. -/
theorem exists_eventually_pintz2023_equation419_remove_threshold
    {eta target C : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hC : 0 < C) :
    ∃ Clog : ℝ, 0 < Clog ∧ ∀ᶠ T : ℝ in atTop,
      ∀ {h N : ℕ},
        h ∈ Finset.range (pintz2023ShellPowerCap data) → 0 < h →
        0 < N →
        let A : ℝ :=
          ((1 / (32 * Real.exp 2 *
                Real.log (pintz2023SourceLambda T k)) /
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
        let p : ℝ :=
          2 * eta - 2 / pintz2023SourceLambda T k +
            2 * (data.epsilon / (100 * (k : ℝ)))
        ∀ count : ℝ, 0 ≤ count →
          count * A ^ 2 ≤
            ((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
                (2 * (2 * Nat.ceil
                  (7 * pintz2023SourceLambda T k) + 1)) : ℕ) *
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k)) *
              (h : ℝ) * 2 * C * (N : ℝ) ^ p →
          count ≤ Clog *
            Real.log T ^ pintz2023ShellLogExponent data * (N : ℝ) ^ p := by
  have hkTwo : 2 ≤ k := le_trans (by omega) hcell.1
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkTwo
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  let B : ℝ := (Real.log 2 + 3) * (Real.log 2)⁻¹ + 2
  let D : ℝ := (Real.log 2)⁻¹ + B
  let Clog : ℝ :=
    136 * (globalLocalZeroLogConstant + 1) * D *
      (pintz2023ShellPowerCap data : ℝ) * C
  have hD : 0 < D := by
    dsimp only [D, B]
    positivity
  have hCap : 0 < pintz2023ShellPowerCap data := by
    unfold pintz2023ShellPowerCap
    omega
  have hClog : 0 < Clog := by
    dsimp only [Clog]
    have := globalLocalZeroLogConstant_pos
    positivity
  have hThresholdEach : ∀ h ∈ Finset.range (pintz2023ShellPowerCap data),
      ∀ᶠ T : ℝ in atTop, 0 < h →
        Real.log T ^ (-(8 * (h : ℝ) + 2)) ≤
          (((1 / (32 * Real.exp 2 *
                Real.log (pintz2023SourceLambda T k)) /
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h /
            h) ^ 2 := by
    intro h hhRange
    by_cases hh : 0 < h
    · exact (eventually_pintz2023_detected_threshold_sq_lower hkTwo hh).mono
        (fun _ hT _ => hT)
    · filter_upwards [] with T
      intro hh'
      exact False.elim (hh hh')
  have hThresholdAll : ∀ᶠ T : ℝ in atTop,
      ∀ h ∈ Finset.range (pintz2023ShellPowerCap data), 0 < h →
        Real.log T ^ (-(8 * (h : ℝ) + 2)) ≤
          (((1 / (32 * Real.exp 2 *
                Real.log (pintz2023SourceLambda T k)) /
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h /
            h) ^ 2 :=
    (Finset.eventually_all (Finset.range
      (pintz2023ShellPowerCap data))).2 hThresholdEach
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  refine ⟨Clog, hClog, ?_⟩
  filter_upwards [hThresholdAll,
    hLambda.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_ge_atTop (Real.exp 1)] with T hThresholdT hLambdaT hT
  intro h N hhRange hh hN
  dsimp only
  intro count hcount hRaw
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTone : 1 ≤ T := (by
    rw [← Real.exp_zero]
    exact (Real.exp_le_exp.mpr zero_le_one).trans hT)
  have hlogOne : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hTPos hT
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
  have hLambdaPos : 0 < pintz2023SourceLambda T k :=
    (Real.exp_pos 1).trans_le hLambdaT
  have hLambdaLeLog : pintz2023SourceLambda T k ≤ Real.log T := by
    unfold pintz2023SourceLambda
    have hratio : 2 / (k : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by exact_mod_cast hkTwo)
    exact mul_le_of_le_one_left (zero_le_one.trans hlogOne) hratio
  have hLocalCeil :
      (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
        (globalLocalZeroLogConstant + 1) * Real.log T := by
    have harg : 0 ≤ globalLocalZeroLogConstant * Real.log T := by
      exact mul_nonneg globalLocalZeroLogConstant_pos.le hlogPos.le
    have hceil := (Nat.ceil_lt_add_one harg).le
    nlinarith
  have hLambdaCeil :
      (Nat.ceil (7 * pintz2023SourceLambda T k) : ℝ) ≤
        8 * Real.log T := by
    have harg : 0 ≤ 7 * pintz2023SourceLambda T k := by positivity
    have hceil := (Nat.ceil_lt_add_one harg).le
    nlinarith
  have hDepthAffine :=
    pintz2023DyadicDepth_cutoff_cast_le_affine hLambdaPos.le
  have hDepth :
      (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) ≤
        D * Real.log T := by
    calc
      _ ≤ (Real.log 2)⁻¹ * pintz2023SourceLambda T k + B := by
        simpa only [B] using hDepthAffine
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B := by gcongr
      _ ≤ (Real.log 2)⁻¹ * Real.log T + B * Real.log T := by
        have hB : 0 ≤ B := by dsimp only [B]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hlogOne hB]
      _ = D * Real.log T := by dsimp only [D]; ring
  have hhCap : (h : ℝ) ≤ pintz2023ShellPowerCap data := by
    exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hhRange)
  have hSelection :
      (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
          (2 * (2 * Nat.ceil
            (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) ≤
        68 * (globalLocalZeroLogConstant + 1) * Real.log T ^ 2 := by
    push_cast
    have hFirst :
        2 * (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
          2 * ((globalLocalZeroLogConstant + 1) * Real.log T) := by
      linarith
    have hSecond :
        2 * (2 * (Nat.ceil (7 * pintz2023SourceLambda T k) : ℝ) + 1) ≤
          34 * Real.log T := by
      nlinarith
    have hFirstUpperNonneg : 0 ≤
        2 * ((globalLocalZeroLogConstant + 1) * Real.log T) := by
      have : 0 ≤ globalLocalZeroLogConstant + 1 := by
        linarith [globalLocalZeroLogConstant_pos]
      positivity
    have hSecondNonneg : 0 ≤
        2 * (2 * (Nat.ceil (7 * pintz2023SourceLambda T k) : ℝ) + 1) := by
      positivity
    calc
      2 * (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) *
          (2 * (2 * (Nat.ceil (7 * pintz2023SourceLambda T k) : ℝ) + 1)) ≤
        (2 * ((globalLocalZeroLogConstant + 1) * Real.log T)) *
          (34 * Real.log T) :=
        mul_le_mul hFirst hSecond hSecondNonneg hFirstUpperNonneg
      _ = 68 * (globalLocalZeroLogConstant + 1) * Real.log T ^ 2 := by
        ring
  have hPrefactor :
      (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
          (2 * (2 * Nat.ceil
            (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) *
        (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) *
        (h : ℝ) * 2 * C ≤ Clog * Real.log T ^ (3 : ℝ) := by
    have hnonneg : 0 ≤
        (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
          (2 * (2 * Nat.ceil
            (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) := by
      positivity
    have hSelectionUpperNonneg : 0 ≤
        68 * (globalLocalZeroLogConstant + 1) * Real.log T ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (by linarith [globalLocalZeroLogConstant_pos]))
        (sq_nonneg _)
    have hDepthNonneg : 0 ≤
        (pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) := by
      positivity
    have hDepthUpperNonneg : 0 ≤ D * Real.log T :=
      mul_nonneg hD.le hlogPos.le
    have hhNonneg : (0 : ℝ) ≤ h := by positivity
    have hCapNonneg : (0 : ℝ) ≤ pintz2023ShellPowerCap data := by
      positivity
    calc
      _ ≤ (68 * (globalLocalZeroLogConstant + 1) * Real.log T ^ 2) *
          (D * Real.log T) * (pintz2023ShellPowerCap data : ℝ) *
          2 * C := by
        gcongr
      _ = Clog * Real.log T ^ (3 : ℝ) := by
        rw [show Real.log T ^ (3 : ℝ) = Real.log T ^ (3 : ℕ) by
          exact Real.rpow_natCast _ 3]
        dsimp only [Clog]
        ring
  let P : ℝ := 8 * (pintz2023ShellPowerCap data : ℝ) + 2
  have hThreshold := hThresholdT h hhRange hh
  have hGlobalThreshold : Real.log T ^ (-P) ≤
      (((1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h) ^ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le hlogOne ?_).trans hThreshold
    dsimp only [P]
    linarith
  have hNpowNonneg : 0 ≤ (N : ℝ) ^
      (2 * eta - 2 / pintz2023SourceLambda T k +
        2 * (data.epsilon / (100 * (k : ℝ)))) := by positivity
  have hRaw' : count *
        (((1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h) ^ 2 ≤
      Clog * Real.log T ^ (3 : ℝ) * (N : ℝ) ^
        (2 * eta - 2 / pintz2023SourceLambda T k +
          2 * (data.epsilon / (100 * (k : ℝ)))) :=
    hRaw.trans (mul_le_mul_of_nonneg_right hPrefactor hNpowNonneg)
  have hLowered : count * Real.log T ^ (-P) ≤
      Clog * Real.log T ^ (3 : ℝ) * (N : ℝ) ^
        (2 * eta - 2 / pintz2023SourceLambda T k +
          2 * (data.epsilon / (100 * (k : ℝ)))) :=
    (mul_le_mul_of_nonneg_left hGlobalThreshold hcount).trans hRaw'
  have hMultiply := mul_le_mul_of_nonneg_right hLowered
    (Real.rpow_nonneg hlogPos.le P)
  have hCancel : Real.log T ^ (-P) * Real.log T ^ P = 1 := by
    rw [← Real.rpow_add hlogPos]
    norm_num
  have hLogs : Real.log T ^ (3 : ℝ) * Real.log T ^ P =
      Real.log T ^ pintz2023ShellLogExponent data := by
    rw [← Real.rpow_add hlogPos]
    unfold pintz2023ShellLogExponent
    dsimp only [P]
    congr 1
    ring
  calc
    count = count * Real.log T ^ (-P) * Real.log T ^ P := by
      rw [mul_assoc, hCancel, mul_one]
    _ ≤ (Clog * Real.log T ^ (3 : ℝ) * (N : ℝ) ^
        (2 * eta - 2 / pintz2023SourceLambda T k +
          2 * (data.epsilon / (100 * (k : ℝ))))) *
        Real.log T ^ P := hMultiply
    _ = Clog * Real.log T ^ pintz2023ShellLogExponent data * (N : ℝ) ^
        (2 * eta - 2 / pintz2023SourceLambda T k +
          2 * (data.epsilon / (100 * (k : ℝ)))) := by
      rw [show
        (Clog * Real.log T ^ (3 : ℝ) * (N : ℝ) ^
              (2 * eta - 2 / pintz2023SourceLambda T k +
                2 * (data.epsilon / (100 * (k : ℝ))))) *
            Real.log T ^ P =
          Clog * (Real.log T ^ (3 : ℝ) * Real.log T ^ P) *
            (N : ℝ) ^
              (2 * eta - 2 / pintz2023SourceLambda T k +
                2 * (data.epsilon / (100 * (k : ℝ)))) by ring]
      rw [hLogs]

#print axioms exists_eventually_pintz2023_equation419_remove_threshold

end

end GafniTao
