import TaoTrudgianYang2025.EnergyPoweredPatterns

/-!
# Logarithmic limits for actual powered patterns

The finite normalization constant may depend on the accuracy but not on the
input scale. The limiting construction must absorb that constant before
choosing the input patterns. The lemmas here keep this requirement explicit.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- Variable power sandwiches determine the logarithmic exponent. -/
theorem tendsto_logb_of_power_sandwich
    (N X err : ℕ → ℝ) (α : ℝ)
    (hN : ∀ n, 1 < N n) (hX : ∀ n, 0 < X n)
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ n, N n ^ (α - err n) ≤ X n ∧ X n ≤ N n ^ (α + err n)) :
    Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds α) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => α - err n) atTop (nhds α) by
      simpa using tendsto_const_nhds.sub herr)
    (show Tendsto (fun n => α + err n) atTop (nhds α) by
      simpa using tendsto_const_nhds.add herr)
  · intro n
    exact (Real.le_logb_iff_rpow_le (hN n) (hX n)).2 (hbound n).1
  · intro n
    exact (Real.logb_le_iff_le_rpow (hN n) (hX n)).2 (hbound n).2

/-- Rebase logarithmic exponents along a genuine change of physical scale. -/
theorem tendsto_logb_rebase
    (N M X : ℕ → ℝ) (α κ : ℝ) (hκ : κ ≠ 0)
    (hN : ∀ n, 1 < N n)
    (hM : Tendsto (fun n => Real.logb (N n) (M n)) atTop (nhds κ))
    (hX : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds α)) :
    Tendsto (fun n => Real.logb (M n) (X n)) atTop (nhds (α / κ)) := by
  apply (hX.div hM hκ).congr
  intro n
  simp only [Real.logb, Pi.div_apply]
  field_simp [(Real.log_pos (hN n)).ne']

/-- Multiplicative constants do not change a logarithmic exponent. -/
theorem tendsto_logb_of_const_mul_sandwich
    (N X Y : ℕ → ℝ) (α a b : ℝ)
    (hN : ∀ n, 1 < N n) (hNtop : Tendsto N atTop atTop)
    (hX : ∀ n, 0 < X n) (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ n, a * X n ≤ Y n ∧ Y n ≤ b * X n)
    (hlim : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds α)) :
    Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds α) := by
  have hlogN := Real.tendsto_log_atTop.comp hNtop
  have hconst (c : ℝ) (hc : 0 < c) :
      Tendsto (fun n => Real.logb (N n) (c * X n)) atTop (nhds α) := by
    have h := (tendsto_const_nhds.div_atTop hlogN :
      Tendsto (fun n => Real.log c / Real.log (N n)) atTop (nhds 0))
    have hsum := h.add hlim
    simpa only [Real.logb, Real.log_mul hc.ne' (hX _).ne', add_div, zero_add] using hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hconst a ha) (hconst b hb)
  · intro n
    exact (Real.logb_le_logb (hN n) (mul_pos ha (hX n))
      ((mul_pos ha (hX n)).trans_le (hbound n).1)).2 (hbound n).1
  · intro n
    exact (Real.logb_le_logb (hN n) ((mul_pos ha (hX n)).trans_le (hbound n).1)
      (mul_pos hb (hX n))).2
      (hbound n).2

/-- Removing the closed interval's left endpoint is negligible in the
logarithmic threshold once the original threshold tends to infinity. -/
theorem tendsto_logb_sub_one
    (N V : ℕ → ℝ) (σ : ℝ)
    (hNtop : Tendsto N atTop atTop) (hVtop : Tendsto V atTop atTop)
    (hlim : Tendsto (fun n => Real.logb (N n) (V n)) atTop (nhds σ)) :
    Tendsto (fun n => Real.logb (N n) (V n - 1)) atTop (nhds σ) := by
  have hdiff : Tendsto (fun n => Real.log (V n - 1) - Real.log (V n))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (Real.tendsto_log_comp_add_sub_log (-1)).comp hVtop
  have hsmall := hdiff.div_atTop (Real.tendsto_log_atTop.comp hNtop)
  have hsum := hsmall.add hlim
  simpa only [Real.logb, Function.comp_apply, sub_div, sub_add_cancel, zero_add] using hsum

/-- The change of scale for any selected powered block has exponent `k`,
even if the selected block varies along the realizing sequence. -/
theorem normalizedPoweredSubpattern_scale_log_limit
    (P : ℕ → LargeValuePattern) (k : ℕ) (C η : ℕ → ℝ)
    (Q : ∀ n, NormalizedPoweredSubpattern (P n) k (C n) (η n))
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop) :
    Tendsto (fun n => Real.logb (P n).N (Q n).pattern.N) atTop (nhds (k : ℝ)) := by
  apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
    (fun n => (P n).N ^ k) (fun n => (Q n).pattern.N) k 1 ((2 : ℝ) ^ k)
    (fun n => (P n).one_lt_N) hNtop
    (fun n => pow_pos (zero_lt_one.trans (P n).one_lt_N) k) zero_lt_one (by positivity)
  · intro n
    simpa only [one_mul] using (Q n).scale_bounds
  · have hEq : (fun n => Real.logb (P n).N ((P n).N ^ k)) = fun _ => (k : ℝ) := by
      funext n
      rw [Real.logb, Real.log_pow]
      field_simp [(Real.log_pos (P n).one_lt_N).ne']
    rw [hEq]
    exact tendsto_const_nhds

/-- Exact normalized threshold formula on logarithmic coordinates. -/
theorem NormalizedPoweredSubpattern.log_value_eq
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η)
    (hV : 1 < P.V) (hC : 0 < C) :
    Real.log Q.pattern.V = k * Real.log (P.V - 1) - Real.log C -
      η * (k * (Real.log 2 + Real.log P.N)) - Real.log k := by
  have hk : 0 < k := Nat.zero_lt_of_lt Q.block.isLt
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hcast : ((2 ^ k * P.scale ^ k : ℕ) : ℝ) = (2 * P.N) ^ k := by
    rw [P.N_eq_scale, mul_pow]
    push_cast
    rfl
  rw [Q.value_eq, hcast]
  rw [Real.log_div (by positivity) (by exact_mod_cast hk.ne'),
    Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_mul hC.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_pow, Real.log_mul (by norm_num) hN.ne']
  ring

/-- Actual normalized thresholds have the expected exponent when the
accuracy tends to zero and its uniform coefficient constant is absorbed
before choosing the realizing scale. -/
theorem normalizedPoweredSubpattern_value_log_limit
    (P : ℕ → LargeValuePattern) (k : ℕ) (C η : ℕ → ℝ) (σ : ℝ)
    (Q : ∀ n, NormalizedPoweredSubpattern (P n) k (C n) (η n))
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hVtop : Tendsto (fun n => (P n).V) atTop atTop)
    (hV : ∀ n, 1 < (P n).V) (hC : ∀ n, 0 < C n)
    (hη : Tendsto η atTop (nhds 0))
    (hClog : Tendsto (fun n => Real.log (C n) / Real.log (P n).N) atTop (nhds 0))
    (hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ)) :
    Tendsto (fun n => Real.logb (P n).N (Q n).pattern.V) atTop (nhds ((k : ℝ) * σ)) := by
  have hminus := tendsto_logb_sub_one (fun n => (P n).N) (fun n => (P n).V)
    σ hNtop hVtop hVlog
  have hlogN := Real.tendsto_log_atTop.comp hNtop
  have hsmall (x : ℝ) : Tendsto (fun n => Real.log x / Real.log (P n).N)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogN
  have hnorm : Tendsto (fun n => η n *
      ((k : ℝ) * (Real.log 2 / Real.log (P n).N + 1))) atTop (nhds 0) := by
    simpa using hη.mul (((hsmall 2).add tendsto_const_nhds).const_mul (k : ℝ))
  have hlim := (((hminus.const_mul (k : ℝ)).sub hClog).sub hnorm).sub (hsmall k)
  simp only [sub_zero] at hlim
  apply hlim.congr
  intro n
  simp only [Real.logb]
  rw [(Q n).log_value_eq (hV n) (hC n)]
  field_simp [(Real.log_pos (P n).one_lt_N).ne']

/-- A positive accuracy sequence bounded by `1/8`. -/
def poweringAccuracy (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 8

theorem poweringAccuracy_pos (n : ℕ) : 0 < poweringAccuracy n := by
  unfold poweringAccuracy
  positivity

theorem poweringAccuracy_le (n : ℕ) : poweringAccuracy n ≤ 1 / 8 := by
  unfold poweringAccuracy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (div_le_one (by positivity)).2 (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem poweringAccuracy_tendsto : Tendsto poweringAccuracy atTop (nhds 0) := by
  simpa only [poweringAccuracy, zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 8

/-- A realizing source family chosen after the sequence of normalization
constants. Every field is derived from actual region membership below. -/
structure PoweringInputFamily (σ τ ρ energy : ℝ) (C : ℕ → ℝ) where
  pattern : ℕ → LargeValuePattern
  scale_top : Tendsto (fun n => (pattern n).N) atTop atTop
  value_top : Tendsto (fun n => (pattern n).V) atTop atTop
  value_gt_one : ∀ n, 1 < (pattern n).V
  card_pos : ∀ n, 0 < ((pattern n).ordinates.card : ℝ)
  energy_pos : ∀ n, 0 < (finsetAdditiveEnergy (pattern n).ordinates : ℝ)
  time_log : Tendsto (fun n => Real.logb (pattern n).N (pattern n).T) atTop (nhds τ)
  value_log : Tendsto (fun n => Real.logb (pattern n).N (pattern n).V) atTop (nhds σ)
  card_log : Tendsto (fun n => Real.logb (pattern n).N
    ((pattern n).ordinates.card : ℝ)) atTop (nhds ρ)
  energy_log : Tendsto (fun n => Real.logb (pattern n).N
    (finsetAdditiveEnergy (pattern n).ordinates : ℝ)) atTop (nhds energy)
  constant_log : Tendsto (fun n => Real.log (C n) / Real.log (pattern n).N) atTop (nhds 0)

/-- Arbitrarily large realizing scales absorb a prescribed sequence of
normalization constants. In particular, this discharges the quantifier
dependency needed when the divisor-bound accuracy tends to zero. -/
theorem exists_powering_input_family
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (C : ℕ → ℝ) : Nonempty (PoweringInputFamily σ τ ρ energy C) := by
  classical
  obtain ⟨s, hs⟩ := h
  let R : ℕ → ℝ := fun n => max ((n : ℝ) + 2)
    (Real.exp (|Real.log (C n)| / poweringAccuracy n + 1))
  have hRpos (n : ℕ) : 0 < R n :=
    (show 0 < (n : ℝ) + 2 by positivity).trans_le (le_max_left _ _)
  have hex (n : ℕ) := hs.2.2.2.2.2
    (poweringAccuracy n) (poweringAccuracy_pos n)
    (poweringAccuracy n) (poweringAccuracy_pos n) (R n) (hRpos n)
  let P : ℕ → LargeValuePattern := fun n => Classical.choose (hex n)
  have hP (n : ℕ) := Classical.choose_spec (hex n)
  change ∀ n, R n ≤ (P n).N ∧ _ at hP
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono (fun n => (le_max_left _ _).trans (hP n).1)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hVlower (n : ℕ) : (P n).N ^ (1 / 4 : ℝ) ≤ (P n).V := by
    calc
      (P n).N ^ (1 / 4 : ℝ) ≤ (P n).N ^ (σ - poweringAccuracy n) := by
        apply Real.rpow_le_rpow_of_exponent_le (P n).one_lt_N.le
        have he := poweringAccuracy_le n
        have hσ := hs.1
        linarith
      _ ≤ (P n).V := (hP n).2.2.2.1
  have hVtop : Tendsto (fun n => (P n).V) atTop atTop :=
    tendsto_atTop_mono hVlower ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hNtop)
  have hVone (n : ℕ) : 1 < (P n).V :=
    (Real.one_lt_rpow (P n).one_lt_N (by norm_num : (0 : ℝ) < 1 / 4)).trans_le (hVlower n)
  have hcard (n : ℕ) : 0 < ((P n).ordinates.card : ℝ) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le
      (hP n).2.2.2.2.2.1
  have henergy (n : ℕ) : 0 < (finsetAdditiveEnergy (P n).ordinates : ℝ) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le
      (hP n).2.2.2.2.2.2.2.1
  refine ⟨{
    pattern := P
    scale_top := hNtop
    value_top := hVtop
    value_gt_one := hVone
    card_pos := hcard
    energy_pos := henergy
    time_log := ?_
    value_log := ?_
    card_log := ?_
    energy_log := ?_
    constant_log := ?_ }⟩
  · apply tendsto_logb_of_power_sandwich _ _ poweringAccuracy τ
      (fun n => (P n).one_lt_N) (fun n => (P n).T_pos) poweringAccuracy_tendsto
    intro n
    exact ⟨(hP n).2.1, (hP n).2.2.1⟩
  · apply tendsto_logb_of_power_sandwich _ _ poweringAccuracy σ
      (fun n => (P n).one_lt_N) (fun n => (P n).V_pos) poweringAccuracy_tendsto
    intro n
    exact ⟨(hP n).2.2.2.1, (hP n).2.2.2.2.1⟩
  · apply tendsto_logb_of_power_sandwich _ _ poweringAccuracy ρ
      (fun n => (P n).one_lt_N) hcard poweringAccuracy_tendsto
    intro n
    exact ⟨(hP n).2.2.2.2.2.1, (hP n).2.2.2.2.2.2.1⟩
  · apply tendsto_logb_of_power_sandwich _ _ poweringAccuracy energy
      (fun n => (P n).one_lt_N) henergy poweringAccuracy_tendsto
    intro n
    exact ⟨(hP n).2.2.2.2.2.2.2.1, (hP n).2.2.2.2.2.2.2.2.1⟩
  · apply squeeze_zero_norm (fun n => ?_) poweringAccuracy_tendsto
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.log_pos (P n).one_lt_N)]
    apply (div_le_iff₀ (Real.log_pos (P n).one_lt_N)).2
    have hlog : |Real.log (C n)| / poweringAccuracy n + 1 ≤ Real.log (P n).N := by
      apply (Real.le_log_iff_exp_le (zero_lt_one.trans (P n).one_lt_N)).2
      exact (le_max_right _ _).trans (hP n).1
    have hmul := mul_le_mul_of_nonneg_left hlog (poweringAccuracy_pos n).le
    rw [mul_add, mul_div_cancel₀ _ (poweringAccuracy_pos n).ne'] at hmul
    nlinarith [poweringAccuracy_pos n]

/-- The actual selected patterns have the powered height exponent and the
original value exponent. Uniform constants are discharged by the source
family's scale choice, not assumed to be absolute across accuracies. -/
theorem PoweringInputFamily.powered_time_value_limits
    {σ τ ρ energy : ℝ} {C : ℕ → ℝ}
    (F : PoweringInputFamily σ τ ρ energy C) (k : ℕ) (hk : 0 < k)
    (hC : ∀ n, 0 < C n)
    (Q : ∀ n, NormalizedPoweredSubpattern (F.pattern n) k (C n) (poweringAccuracy n)) :
    Tendsto (fun n => (Q n).pattern.N) atTop atTop ∧
    Tendsto (fun n => Real.logb (Q n).pattern.N (Q n).pattern.T) atTop (nhds (τ / k)) ∧
    Tendsto (fun n => Real.logb (Q n).pattern.N (Q n).pattern.V) atTop (nhds σ) := by
  have hscale := normalizedPoweredSubpattern_scale_log_limit F.pattern k C poweringAccuracy Q F.scale_top
  have hvalue := normalizedPoweredSubpattern_value_log_limit F.pattern k C poweringAccuracy σ Q
    F.scale_top F.value_top F.value_gt_one hC poweringAccuracy_tendsto F.constant_log F.value_log
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_atTop_mono (fun n => ?_) F.scale_top
    calc
      (F.pattern n).N = (F.pattern n).N ^ 1 := (pow_one _).symm
      _ ≤ (F.pattern n).N ^ k := pow_le_pow_right₀ (F.pattern n).one_lt_N.le (by omega)
      _ ≤ (Q n).pattern.N := (Q n).scale_bounds.1
  · have ht := tendsto_logb_rebase (fun n => (F.pattern n).N) (fun n => (Q n).pattern.N)
      (fun n => (F.pattern n).T) τ k hkReal (fun n => (F.pattern n).one_lt_N) hscale F.time_log
    simpa only [(Q _).time_eq] using ht
  · have hv := tendsto_logb_rebase (fun n => (F.pattern n).N) (fun n => (Q n).pattern.N)
      (fun n => (Q n).pattern.V) (k * σ) k hkReal (fun n => (F.pattern n).one_lt_N) hscale hvalue
    simpa only [mul_div_cancel_left₀ σ hkReal] using hv

/-- Compactness extracts all three energy coordinates from an actual
asymptotic pattern family. The double-zeta coordinate is extracted afresh;
there is no relation to any input double-zeta exponent. -/
theorem energyRegion_subsequence_of_log_limits
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (P : ℕ → LargeValuePattern)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hcard : ∀ n, 0 < ((P n).ordinates.card : ℝ)) :
    ∃ x : ℝ × ℝ × ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => energyLogCoordinates (P (φ n))) atTop (nhds x) ∧
      InLargeValueEnergyRegion σ τ x.1 x.2.1 x.2.2 := by
  have henergy (n : ℕ) : 0 < (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
    have h : ((P n).ordinates.card : ℝ) ^ 2 ≤
        (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
      exact_mod_cast finset_card_square_le_additiveEnergy (P n).ordinates
    exact (sq_pos_of_pos (hcard n)).trans_le h
  have hsum (n : ℕ) : 0 < doubleZetaSum (P n) := by
    have hi : 0 < ((P n).indices.card : ℝ) :=
      (zero_lt_one.trans (P n).one_lt_N).trans_le (P n).N_le_indices_card_cast
    exact (mul_pos (hcard n) (sq_pos_of_pos hi)).trans_le (doubleZetaSum_diagonal_lower (P n))
  have hbounded : ∀ᶠ n in atTop, energyLogCoordinates (P n) ∈
      Set.Icc (0, 0, 0) (τ + 2, 3 * τ + 8, 2 * τ + 8) := by
    filter_upwards [hNtop.eventually (eventually_ge_atTop 2),
      hTlog.eventually (eventually_lt_nhds (lt_add_one τ))] with n hN hT
    apply energyLogCoordinates_mem_box (P n) hτ zero_lt_one le_rfl hN
      ((Real.logb_le_iff_le_rpow (P n).one_lt_N (P n).T_pos).1 hT.le)
      (hcard n) (henergy n) (hsum n)
  obtain ⟨x, hx, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq' hbounded.frequently
  have hφtop := hφ.tendsto_atTop
  have hcardlim : Tendsto (fun n => Real.logb (P (φ n)).N
      ((P (φ n)).ordinates.card : ℝ)) atTop (nhds x.1) := by
    simpa only [Function.comp_def, energyLogCoordinates] using
      (continuous_fst.tendsto x).comp hlim
  have henergylim : Tendsto (fun n => Real.logb (P (φ n)).N
      (finsetAdditiveEnergy (P (φ n)).ordinates : ℝ)) atTop (nhds x.2.1) := by
    simpa only [Function.comp_def, energyLogCoordinates] using
      ((continuous_fst.comp continuous_snd).tendsto x).comp hlim
  have hsumlim : Tendsto (fun n => Real.logb (P (φ n)).N
      (doubleZetaSum (P (φ n)))) atTop (nhds x.2.2) := by
    simpa only [Function.comp_def, energyLogCoordinates] using
      ((continuous_snd.comp continuous_snd).tendsto x).comp hlim
  refine ⟨x, φ, hφ, hlim, ?_⟩
  apply inLargeValueEnergyRegionAsymptotic_iff.mp
  refine ⟨hσLower, hσUpper, hτ, hx.1.1, hx.1.2.1,
    ⟨fun n => P (φ n), hNtop.comp hφtop, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Expdb.isPowerAsymptotic_of_logb_tendsto
      (Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Eventually.of_forall fun n => (P (φ n)).T_pos) (hTlog.comp hφtop)
  · exact Expdb.isPowerAsymptotic_of_logb_tendsto
      (Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Eventually.of_forall fun n => (P (φ n)).V_pos) (hVlog.comp hφtop)
  · exact Expdb.isPowerAsymptotic_of_logb_tendsto
      (Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Eventually.of_forall fun n => hcard (φ n)) hcardlim
  · exact Expdb.isPowerAsymptotic_of_logb_tendsto
      (Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Eventually.of_forall fun n => henergy (φ n)) henergylim
  · exact Expdb.isPowerAsymptotic_of_logb_tendsto
      (Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Eventually.of_forall fun n => hsum (φ n)) hsumlim

end TaoTrudgianYang2025
