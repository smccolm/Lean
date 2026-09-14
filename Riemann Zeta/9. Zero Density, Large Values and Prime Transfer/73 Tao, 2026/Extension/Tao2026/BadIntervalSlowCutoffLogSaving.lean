import Tao2026.BadIntervalSlowCutoff
import Tao2026.BadIntervalLargePrimeErrorPower
import Tao2026.BadIntervalTypicalAntiSieve

/-!
# Logarithmic saving for the Proposition 6.5 slow diagonal

The fixed-row power saving from `BadIntervalSlowCutoff` is stronger than a
fixed power of `log x`.  This module records that conversion after the
large-prime error normalization is available, and then performs the same
countable diagonal while retaining a logarithmic saving whose exponent tends
to one.
-/

namespace Tao2026

open Filter Topology

noncomputable section

/-- The logarithmic exponent retained in the `n`th fixed row. -/
def taoSlowLogSavingExponent (n : ℕ) : ℝ :=
  1 - 1 / (taoSlowCutoffDenominator n : ℝ)

theorem taoSlowLogSavingExponent_nonneg (n : ℕ) :
    0 ≤ taoSlowLogSavingExponent n := by
  have hd : (1 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast (show 1 ≤ taoSlowCutoffDenominator n from
      (by have := ten_le_taoSlowCutoffDenominator n; omega))
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by positivity
  rw [taoSlowLogSavingExponent]
  have hrecip : 1 / (taoSlowCutoffDenominator n : ℝ) ≤ 1 :=
    (div_le_one hdPos).2 hd
  linarith

theorem taoSlowLogSavingExponent_le_one (n : ℕ) :
    taoSlowLogSavingExponent n ≤ 1 := by
  rw [taoSlowLogSavingExponent]
  have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  have hrecip : 0 ≤ 1 / (taoSlowCutoffDenominator n : ℝ) := by positivity
  linarith

/-- The fixed-row `z`-power margin implies a logarithmic saving. -/
theorem eventually_card_taoSlowNonTypicalFailureUnion_le_logSaving (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) /
          Real.log x ^ taoSlowLogSavingExponent n := by
  let δ : ℝ := 1 / (128 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have habsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := (2 : ℝ)) (k := (2 : ℝ)) (a := δ) (b := (0 : ℝ))
      (by norm_num) hδ
  filter_upwards
    [eventually_card_taoSlowNonTypicalFailureUnion_le n,
     habsorb,
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
       (eventually_ge_atTop (1 : ℝ)),
     tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hcard habsorbX hlogOne hiterOne
  have hlogPos : 0 < Real.log x := zero_lt_one.trans_le hlogOne
  have hiterPos : 0 < iteratedLog x := zero_lt_one.trans_le hiterOne
  have hzδPos : 0 < (taoZ x) ^ δ :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  have habsorbX' :
      2 * Real.log (taoZ x) ^ (2 : ℕ) ≤ (taoZ x) ^ δ := by
    rw [Real.rpow_zero, div_one] at habsorbX
    have hlogEq : Real.log (taoZ x) ^ (2 : ℝ) =
        Real.log (taoZ x) ^ (2 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hlogEq] at habsorbX
    exact (div_le_one hzδPos).mp habsorbX
  have hlogLe : Real.log x ≤ 2 * Real.log (taoZ x) ^ (2 : ℕ) := by
    rw [log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogPos hiterPos]
    exact div_le_self (by positivity) hiterOne
  have hlogPowLeLog :
      Real.log x ^ taoSlowLogSavingExponent n ≤ Real.log x := by
    calc
      Real.log x ^ taoSlowLogSavingExponent n ≤ Real.log x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne
          (taoSlowLogSavingExponent_le_one n)
      _ = Real.log x := Real.rpow_one _
  have hlogPowLeZ :
      Real.log x ^ taoSlowLogSavingExponent n ≤ (taoZ x) ^ δ :=
    hlogPowLeLog.trans (hlogLe.trans habsorbX')
  have hlogPowPos : 0 < Real.log x ^ taoSlowLogSavingExponent n :=
    Real.rpow_pos_of_pos hlogPos _
  have hnormalized :
      (x : ℝ) / (taoZ x) ^ (2 + δ) =
        ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) / (taoZ x) ^ δ := by
    rw [Real.rpow_add (taoZ_pos x)]
    ring
  calc
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ (2 + δ) := by
      simpa only [δ] using hcard
    _ = ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) / (taoZ x) ^ δ := hnormalized
    _ ≤ ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) /
        Real.log x ^ taoSlowLogSavingExponent n :=
      div_le_div_of_nonneg_left
        (div_nonneg (Nat.cast_nonneg x)
          (Real.rpow_nonneg (taoZ_pos x).le _))
        hlogPowPos hlogPowLeZ

/-- The same fixed-row estimate normalized by the actual one-term bad-set
count.  Half of the row's `z`-power margin pays for Lemma 1.6(i), while the
other half absorbs the logarithmic factor. -/
theorem eventually_card_taoSlowNonTypicalFailureUnion_le_badOneTermCount_div_logSaving
    (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        (badOneTermCount x : ℝ) /
          Real.log x ^ taoSlowLogSavingExponent n := by
  let δ : ℝ := 1 / (256 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have habsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := (2 : ℝ)) (k := (2 : ℝ)) (a := δ) (b := (0 : ℝ))
      (by norm_num) hδ
  filter_upwards
    [eventually_card_taoSlowNonTypicalFailureUnion_le n,
     eventually_self_div_taoZ_rpow_le_badOneTermCount hδ,
     habsorb,
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
       (eventually_ge_atTop (1 : ℝ)),
     tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hcard hOneTerm habsorbX hlogOne hiterOne
  have hlogPos : 0 < Real.log x := zero_lt_one.trans_le hlogOne
  have hiterPos : 0 < iteratedLog x := zero_lt_one.trans_le hiterOne
  have hzδPos : 0 < (taoZ x) ^ δ :=
    Real.rpow_pos_of_pos (taoZ_pos x) _
  have habsorbX' :
      2 * Real.log (taoZ x) ^ (2 : ℕ) ≤ (taoZ x) ^ δ := by
    rw [Real.rpow_zero, div_one] at habsorbX
    have hlogEq : Real.log (taoZ x) ^ (2 : ℝ) =
        Real.log (taoZ x) ^ (2 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hlogEq] at habsorbX
    exact (div_le_one hzδPos).mp habsorbX
  have hlogLe : Real.log x ≤ 2 * Real.log (taoZ x) ^ (2 : ℕ) := by
    rw [log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogPos hiterPos]
    exact div_le_self (by positivity) hiterOne
  have hlogPowLeZ :
      Real.log x ^ taoSlowLogSavingExponent n ≤ (taoZ x) ^ δ := by
    calc
      Real.log x ^ taoSlowLogSavingExponent n ≤ Real.log x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne
          (taoSlowLogSavingExponent_le_one n)
      _ = Real.log x := Real.rpow_one _
      _ ≤ 2 * Real.log (taoZ x) ^ (2 : ℕ) := hlogLe
      _ ≤ (taoZ x) ^ δ := habsorbX'
  have hlogPowPos : 0 < Real.log x ^ taoSlowLogSavingExponent n :=
    Real.rpow_pos_of_pos hlogPos _
  have hexponent :
      2 + 1 / (128 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        (2 + δ) + δ := by
    dsimp only [δ]
    have hd : (taoSlowCutoffDenominator n : ℝ) ≠ 0 := by
      exact_mod_cast (taoSlowCutoffDenominator_pos n).ne'
    field_simp
    ring
  have hnormalized :
      (x : ℝ) / (taoZ x) ^ ((2 + δ) + δ) =
        ((x : ℝ) / (taoZ x) ^ (2 + δ)) / (taoZ x) ^ δ := by
    rw [Real.rpow_add (taoZ_pos x)]
    ring
  calc
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ ((2 + δ) + δ) := by
      rw [← hexponent]
      exact hcard
    _ = ((x : ℝ) / (taoZ x) ^ (2 + δ)) / (taoZ x) ^ δ := hnormalized
    _ ≤ ((x : ℝ) / (taoZ x) ^ (2 + δ)) /
        Real.log x ^ taoSlowLogSavingExponent n :=
      div_le_div_of_nonneg_left
        (div_nonneg (Nat.cast_nonneg x)
          (Real.rpow_nonneg (taoZ_pos x).le _))
        hlogPowPos hlogPowLeZ
    _ ≤ (badOneTermCount x : ℝ) /
        Real.log x ^ taoSlowLogSavingExponent n :=
      div_le_div_of_nonneg_right hOneTerm hlogPowPos.le

/-- A row selector tending to infinity makes the retained logarithmic
exponent tend to one. -/
theorem tendsto_taoSlowLogSavingExponent_comp
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x => taoSlowLogSavingExponent (q x)) atTop (𝓝 1) := by
  have hdNat : Tendsto (fun x => taoSlowCutoffDenominator (q x))
      atTop atTop := by
    rw [tendsto_atTop_atTop] at hq ⊢
    intro b
    obtain ⟨a, ha⟩ := hq b
    refine ⟨a, fun x hx => ?_⟩
    unfold taoSlowCutoffDenominator
    exact (ha x hx).trans (Nat.le_add_right (q x) 10)
  have hdReal : Tendsto
      (fun x => (taoSlowCutoffDenominator (q x) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdNat
  have hquot : Tendsto
      (fun x => (1 : ℝ) / (taoSlowCutoffDenominator (q x) : ℝ))
      atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using hone.div_atTop hdReal
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  convert hone.sub hquot using 1
  all_goals norm_num [taoSlowLogSavingExponent]

/-- Proposition 6.5 with one slow selector, exact source cutoff asymptotics,
and a logarithmic saving exponent converging to one. -/
theorem exists_taoProposition65_slowDiagonal_logSaving :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x => taoSlowLogSavingExponent (q x)) atTop (𝓝 1) ∧
      ∀ᶠ x : ℕ in atTop,
        ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
          ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) /
            Real.log x ^ taoSlowLogSavingExponent (q x) := by
  let P : ℕ → ℕ → Prop := fun n x =>
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
      ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) /
        Real.log x ^ taoSlowLogSavingExponent n
  have hP : ∀ n, ∀ᶠ x : ℕ in atTop, P n x := by
    intro n
    simpa only [P] using
      eventually_card_taoSlowNonTypicalFailureUnion_le_logSaving n
  obtain ⟨q, hq, hselected⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  exact ⟨q, hq, tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq,
    tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq,
    tendsto_taoSlowLogSavingExponent_comp hq,
    by simpa only [P] using hselected⟩

/-- The diagonal normalized by the actual one-term bad-set count. -/
theorem exists_taoProposition65_slowDiagonal_badOneTerm_logSaving :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x => taoSlowLogSavingExponent (q x)) atTop (𝓝 1) ∧
      ∀ᶠ x : ℕ in atTop,
        ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
          (badOneTermCount x : ℝ) /
            Real.log x ^ taoSlowLogSavingExponent (q x) := by
  let P : ℕ → ℕ → Prop := fun n x =>
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
      (badOneTermCount x : ℝ) /
        Real.log x ^ taoSlowLogSavingExponent n
  have hP : ∀ n, ∀ᶠ x : ℕ in atTop, P n x := by
    intro n
    simpa only [P] using
      eventually_card_taoSlowNonTypicalFailureUnion_le_badOneTermCount_div_logSaving n
  obtain ⟨q, hq, hselected⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  exact ⟨q, hq, tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq,
    tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq,
    tendsto_taoSlowLogSavingExponent_comp hq,
    by simpa only [P] using hselected⟩

/-- The selected non-typical union is bounded by the one-term count divided
by every fixed logarithmic power below one. -/
theorem exists_taoProposition65_slowDiagonal_badOneTerm_every_logSaving :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℕ in atTop,
          ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
            (badOneTermCount x : ℝ) / Real.log x ^ (1 - ε) := by
  obtain ⟨q, hq, hlower, hupper, hexponent, hbound⟩ :=
    exists_taoProposition65_slowDiagonal_badOneTerm_logSaving
  refine ⟨q, hq, hlower, hupper, ?_⟩
  intro ε hε
  have hexponentLower : ∀ᶠ x : ℕ in atTop,
      1 - ε ≤ taoSlowLogSavingExponent (q x) :=
    hexponent.eventually (Ici_mem_nhds (sub_lt_self 1 hε))
  filter_upwards
    [hbound, hexponentLower,
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
       (eventually_ge_atTop (1 : ℝ))]
      with x hx hα hlogOne
  have htargetPos : 0 < Real.log x ^ (1 - ε) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hpow : Real.log x ^ (1 - ε) ≤
      Real.log x ^ taoSlowLogSavingExponent (q x) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne hα
  exact hx.trans (div_le_div_of_nonneg_left
    (Nat.cast_nonneg (badOneTermCount x)) htargetPos hpow)

/-- Source-facing form: the selected non-typical union saves every fixed
power `log(x)^(1-ε)` below the limiting exponent one. -/
theorem exists_taoProposition65_slowDiagonal_every_logSaving :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℕ in atTop,
          ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
            ((x : ℝ) / (taoZ x) ^ (2 : ℝ)) /
              Real.log x ^ (1 - ε) := by
  obtain ⟨q, hq, hlower, hupper, hexponent, hbound⟩ :=
    exists_taoProposition65_slowDiagonal_logSaving
  refine ⟨q, hq, hlower, hupper, ?_⟩
  intro ε hε
  have hexponentLower : ∀ᶠ x : ℕ in atTop,
      1 - ε ≤ taoSlowLogSavingExponent (q x) :=
    hexponent.eventually (Ici_mem_nhds (sub_lt_self 1 hε))
  filter_upwards
    [hbound, hexponentLower,
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
       (eventually_ge_atTop (1 : ℝ))]
      with x hx hα hlogOne
  have htargetPos : 0 < Real.log x ^ (1 - ε) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hpow : Real.log x ^ (1 - ε) ≤
      Real.log x ^ taoSlowLogSavingExponent (q x) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne hα
  exact hx.trans (div_le_div_of_nonneg_left
    (div_nonneg (Nat.cast_nonneg x)
      (Real.rpow_nonneg (taoZ_pos x).le _)) htargetPos hpow)

end

end Tao2026
