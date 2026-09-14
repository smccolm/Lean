import Tao2026.BadIntervalTypicalAssembly

/-!
# Length-weighted assembly of the typical prime-tuple count

An interval of dyadic length `2^r` contributes at most `2^r` integers to its
union.  This module inserts that weight into the complete typical tuple count.
The weight cancels the reciprocal `2^r` in Proposition 6.6, leaving only the
number of admissible dyadic exponents.  That number is `O(log₂ x)`, and the
resulting assembly factor still tends to zero.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

def taoPrimeTupleTypicalDyadicLengthWeight
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) : ℕ :=
  ∑ a ∈ taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime,
    2 ^ a.1

theorem taoPrimeTupleTypicalDyadicLengthWeight_eq_sum
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    taoPrimeTupleTypicalDyadicLengthWeight P x lowerPrime upperPrime =
      ∑ r ∈ badIntervalTypicalDyadicExponents x,
        2 ^ r * (taoPrimeTupleTypicalRemainderPairs P x (2 ^ r)
          lowerPrime upperPrime).card := by
  rw [taoPrimeTupleTypicalDyadicLengthWeight, taoPrimeTupleTypicalDyadicRemainderTriples,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  simp [Nat.mul_comm]

theorem eventually_card_badIntervalTypicalDyadicExponents_cast_le_fifty_mul_iteratedLog :
    ∀ᶠ x : ℕ in atTop,
      ((badIntervalTypicalDyadicExponents x).card : ℝ) ≤
        50 * iteratedLog x := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ))] with x hx
  have hlogPos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  have hpowNonneg : 0 ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := by positivity
  have hpowOne : 1 ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := by
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (x : ℝ))
  have hcutoffLt : (taoTypicalLengthCutoff x : ℝ) <
      2 * (Real.log (x : ℝ)) ^ (20 : ℕ) := by
    have hceil : (taoTypicalLengthCutoff x : ℝ) <
        (Real.log (x : ℝ)) ^ (20 : ℕ) + 1 := by
      simpa only [taoTypicalLengthCutoff] using
        Nat.ceil_lt_add_one hpowNonneg
    linarith
  have hcutoffPos : 0 < taoTypicalLengthCutoff x := by
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlogPos 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  have hcutoffOne : (1 : ℝ) ≤ taoTypicalLengthCutoff x := by
    exact_mod_cast hcutoffPos
  have hlogCutoffNonneg : 0 ≤ Real.log (taoTypicalLengthCutoff x : ℝ) :=
    Real.log_nonneg hcutoffOne
  have hlogCutoff : Real.log (taoTypicalLengthCutoff x : ℝ) ≤
      Real.log 2 + 20 * iteratedLog x := by
    have hmono := Real.log_le_log (by exact_mod_cast hcutoffPos) hcutoffLt.le
    rw [Real.log_mul (by norm_num) (pow_ne_zero 20 hlogPos.ne'),
      Real.log_pow] at hmono
    simpa only [iteratedLog, Nat.cast_ofNat] using hmono
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hnatLog : (Nat.log 2 (taoTypicalLengthCutoff x) : ℝ) ≤
      2 * Real.log (taoTypicalLengthCutoff x : ℝ) := by
    have hbase := badInterval_natLogTwo_cast_le_log_div hcutoffPos
    refine hbase.trans ?_
    apply (div_le_iff₀ hlogTwoPos).2
    nlinarith
  have hiterLogTwo : Real.log 2 ≤ iteratedLog x := by
    unfold iteratedLog
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hlogPos hx
  have hiterHalf : (1 / 2 : ℝ) ≤ iteratedLog x :=
    le_trans hlogTwoHalf.le hiterLogTwo
  rw [badIntervalTypicalDyadicExponents, Finset.card_range]
  push_cast
  nlinarith

theorem eventually_taoPrimeTupleTypicalDyadicLengthWeight_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleTypicalDyadicLengthWeight (P x) x (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
        ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
              (8 * iteratedLog x) ^ (50 : ℕ) /
                Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  have hpair :=
    eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hpair, eventually_ge_atTop (2 : ℕ)] with x hx hxTwo
  rw [taoPrimeTupleTypicalDyadicLengthWeight_eq_sum, Nat.cast_sum]
  let K : ℝ :=
    (psiNat (taoPrimeTupleRemainderBudget x (P x))
        (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
      ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxTwo)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  calc
    (∑ r ∈ badIntervalTypicalDyadicExponents x,
        ((2 ^ r * (taoPrimeTupleTypicalRemainderPairs (P x) x (2 ^ r)
          (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℕ) : ℝ)) ≤
        ∑ _r ∈ badIntervalTypicalDyadicExponents x, K := by
      apply Finset.sum_le_sum
      intro r hr
      have hrle : r ≤ Nat.log 2 (taoTypicalLengthCutoff x) := by
        simp only [badIntervalTypicalDyadicExponents, Finset.mem_range] at hr
        omega
      have hpowle : 2 ^ r ≤ taoTypicalLengthCutoff x :=
        (Nat.pow_le_pow_right (by norm_num) hrle).trans
          (Nat.pow_log_le_self 2 hcutoff.ne')
      have hpowpos : 1 ≤ (2 : ℕ) ^ r := by
        have : 0 < (2 : ℕ) ^ r := pow_pos (by norm_num) r
        omega
      have hbound := hx (2 ^ r) hpowpos hpowle
      have hcastPos : (0 : ℝ) ≤ ((2 : ℕ) ^ r : ℕ) := by positivity
      calc
        ((2 ^ r * (taoPrimeTupleTypicalRemainderPairs (P x) x (2 ^ r)
            (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℕ) : ℝ) =
            (((2 : ℕ) ^ r : ℕ) : ℝ) *
              ((taoPrimeTupleTypicalRemainderPairs (P x) x (2 ^ r)
                (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℝ) := by
          push_cast
          rfl
        _ ≤ (((2 : ℕ) ^ r : ℕ) : ℝ) *
            ((psiNat (taoPrimeTupleRemainderBudget x (P x))
                (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
              ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                    (8 * iteratedLog x) ^ (50 : ℕ) /
                  ((((2 : ℕ) ^ r : ℕ) : ℝ) *
                    Real.log (taoZ x) ^ (2 : ℕ))) *
                ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))) :=
          mul_le_mul_of_nonneg_left hbound hcastPos
        _ = K := by
          dsimp only [K]
          field_simp [show ((((2 : ℕ) ^ r : ℕ) : ℝ)) ≠ 0 by positivity]
    _ = ((badIntervalTypicalDyadicExponents x).card : ℝ) * K := by
      simp
    _ = ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
              (8 * iteratedLog x) ^ (50 : ℕ) /
                Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
      dsimp only [K]
      ring

def TaoPrimeTupleSlowScaleWeightedCountBound
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q : ℕ → ℕ) (x : ℕ) (R : Fin 1001 → ℕ) : Prop :=
  (taoPrimeTupleTypicalDyadicLengthWeight (fun j => 2 ^ R j) x
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
      (psiNat
        (taoPrimeTupleRemainderBudget x (fun j => 2 ^ R j))
        (taoPrimeTupleRemainderSmoothnessCutoff
          (fun j => 2 ^ R j)) : ℝ) *
      ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (2 ^ R j)).card : ℝ))

theorem eventually_taoPrimeTupleSlowScaleWeightedCountBound_of_selector
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    ∀ᶠ x : ℕ in atTop,
      TaoPrimeTupleSlowScaleWeightedCountBound hC hburgess q x (R x) := by
  let P : ℕ → Fin 1001 → ℕ := fun x =>
    taoPrimeTupleRepairScale (fun j => 2 ^ R x j)
  have hscale : TaoPrimeTupleSourceScaleFamily P := by
    simpa only [P] using
      taoPrimeTupleSourceScaleFamily_repaired_slowScaleExponentTupleSelector
        hq hR
  have hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty := by
    intro x j
    exact taoPrimeTupleRepairScale_band_nonempty _ _
  have hcount := eventually_taoPrimeTupleTypicalDyadicLengthWeight_le hC hburgess hscale hP
    (taoPrimeTupleSlowLowerCutoff q)
  filter_upwards [hcount,
    eventually_taoPrimeTupleRepairScale_slowSelector_eq hR] with x hx heq
  simpa only [P, heq, TaoPrimeTupleSlowScaleWeightedCountBound] using hx

theorem eventually_forall_taoPrimeTupleSlowScaleWeightedCountBound_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop, ∀ R ∈ taoPrimeTupleSlowScaleExponentTuples q x,
      TaoPrimeTupleSlowScaleWeightedCountBound hC hburgess q x R := by
  let S : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    R ∈ taoPrimeTupleSlowScaleExponentTuples q x
  let Q : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    TaoPrimeTupleSlowScaleWeightedCountBound hC hburgess q x R
  have hne : ∀ᶠ x : ℕ in atTop, ∃ R, S x R :=
    Filter.Eventually.of_forall fun x => by
      simpa only [S] using taoPrimeTupleSlowScaleExponentTuples_nonempty q x
  have hselector : ∀ f : ℕ → (Fin 1001 → ℕ),
      (∀ᶠ x : ℕ in atTop, S x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    have hcount := eventually_taoPrimeTupleSlowScaleWeightedCountBound_of_selector
      hC hburgess hq (by simpa only [S] using hf)
    simpa only [Q] using hcount
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx R hR
  exact hx R hR

theorem eventually_forall_taoPrimeTupleSlowOrderedScaleWeightedCountBound_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        TaoPrimeTupleSlowScaleWeightedCountBound hC hburgess q x R := by
  filter_upwards [eventually_forall_taoPrimeTupleSlowScaleWeightedCountBound_of_explicitBurgess
    hC hburgess hq] with x hx R hR
  exact hx R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

def taoPrimeTupleTypicalWeightedAssemblyFactor
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) (x : ℕ) : ℝ :=
  ((badIntervalTypicalDyadicExponents x).card : ℝ) *
    (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
      (8 * iteratedLog x) ^ (50 : ℕ) /
        Real.log (taoZ x) ^ (2 : ℕ)) *
    8 ^ (1001 : ℕ)

theorem taoPrimeTupleTypicalWeightedAssemblyFactor_nonneg
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) (x : ℕ) :
    0 ≤ taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x := by
  unfold taoPrimeTupleTypicalWeightedAssemblyFactor
  have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
  positivity

theorem tendsto_taoPrimeTupleTypicalWeightedAssemblyFactor_zero
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    Tendsto (taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess)
      atTop (𝓝 0) := by
  let B : ℝ := taoPrimeTupleTypicalUniformSourceConstant hC hburgess
  let M : ℝ := (8 : ℝ) ^ (1001 : ℕ)
  have hB : 0 < B := by
    exact taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun x : ℕ =>
      iteratedLog x ^ (50 : ℕ) / Real.log x) atTop (𝓝 0) := by
    simpa only [iteratedLog] using
      (Real.isLittleO_pow_log_id_atTop (n := 50)).tendsto_div_nhds_zero.comp hlog
  have hscaled : Tendsto (fun x : ℕ =>
      (100 * B * 8 ^ (50 : ℕ) * M) *
        (iteratedLog x ^ (50 : ℕ) / Real.log x)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbase
  have halgebra (b m i l : ℝ) (hi : i ≠ 0) (hl : l ≠ 0) :
      (50 * i) * (b * (8 * i) ^ (50 : ℕ) / (l * i / 2)) * m =
        (100 * b * 8 ^ (50 : ℕ) * m) * (i ^ (50 : ℕ) / l) := by
    rw [mul_pow]
    field_simp [hi, hl]
    ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x =>
      taoPrimeTupleTypicalWeightedAssemblyFactor_nonneg hC hburgess x
  · filter_upwards
      [eventually_card_badIntervalTypicalDyadicExponents_cast_le_fifty_mul_iteratedLog,
       hlog.eventually (eventually_gt_atTop (0 : ℝ)),
       tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
        with x hcard hlogX hiterX
    have hidentity :=
      log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogX hiterX
    have hidentity' := (eq_div_iff hiterX.ne').mp hidentity
    have hdenominator :
        Real.log (taoZ x) ^ (2 : ℕ) =
          Real.log x * iteratedLog x / 2 := by
      nlinarith [hidentity']
    change
      ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (B * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) * M ≤
        (100 * B * 8 ^ (50 : ℕ) * M) *
          (iteratedLog x ^ (50 : ℕ) / Real.log x)
    calc
      ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (B * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) * M ≤
        (50 * iteratedLog x) *
          (B * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) * M := by
        gcongr
      _ = (100 * B * 8 ^ (50 : ℕ) * M) *
          (iteratedLog x ^ (50 : ℕ) / Real.log x) := by
        rw [hdenominator]
        exact halgebra B M (iteratedLog x) (Real.log x)
          hiterX.ne' hlogX.ne'
  · exact hscaled

/-- Quantitative form of the weighted assembly estimate before the final
polylogarithmic absorption. -/
theorem eventually_taoPrimeTupleTypicalWeightedAssemblyFactor_le_logEnvelope
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x ≤
        (100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)) *
            (iteratedLog x ^ (50 : ℕ) / Real.log x) := by
  let B : ℝ := taoPrimeTupleTypicalUniformSourceConstant hC hburgess
  let M : ℝ := (8 : ℝ) ^ (1001 : ℕ)
  have hB : 0 < B := by
    exact taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
  have halgebra (b m i l : ℝ) (hi : i ≠ 0) (hl : l ≠ 0) :
      (50 * i) * (b * (8 * i) ^ (50 : ℕ) / (l * i / 2)) * m =
        (100 * b * 8 ^ (50 : ℕ) * m) * (i ^ (50 : ℕ) / l) := by
    rw [mul_pow]
    field_simp [hi, hl]
    ring
  filter_upwards
    [eventually_card_badIntervalTypicalDyadicExponents_cast_le_fifty_mul_iteratedLog,
     (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ)),
     tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with x hcard hlogX hiterX
  have hidentity :=
    log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogX hiterX
  have hidentity' := (eq_div_iff hiterX.ne').mp hidentity
  have hdenominator :
      Real.log (taoZ x) ^ (2 : ℕ) =
        Real.log x * iteratedLog x / 2 := by
    nlinarith [hidentity']
  change
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
        (B * (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ)) * M ≤
      (100 * B * 8 ^ (50 : ℕ) * M) *
        (iteratedLog x ^ (50 : ℕ) / Real.log x)
  calc
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
        (B * (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ)) * M ≤
      (50 * iteratedLog x) *
        (B * (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ)) * M := by
      gcongr
    _ = (100 * B * 8 ^ (50 : ℕ) * M) *
        (iteratedLog x ^ (50 : ℕ) / Real.log x) := by
      rw [hdenominator]
      exact halgebra B M (iteratedLog x) (Real.log x)
        hiterX.ne' hlogX.ne'

/-- The weighted assembly factor retains the source's full logarithmic saving,
up to an arbitrary fixed positive slack. -/
theorem eventually_taoPrimeTupleTypicalWeightedAssemblyFactor_le_logSaving
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x ≤
        (100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)) /
            Real.log x ^ (1 - ε) := by
  let K : ℝ :=
    100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
      8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (50 : ℝ) hε).comp_tendsto hlog
  have hgrowth := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards
    [eventually_taoPrimeTupleTypicalWeightedAssemblyFactor_le_logEnvelope
      hC hburgess,
     hlog.eventually (eventually_gt_atTop (1 : ℝ)),
     tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
     hgrowth] with x henvelope hlogX hiterX hgrowthX
  have hiterPow :
      iteratedLog x ^ (50 : ℕ) ≤ Real.log x ^ ε := by
    have hrightPos : 0 < Real.log x ^ ε :=
      Real.rpow_pos_of_pos (zero_lt_one.trans hlogX) _
    change ‖Real.log (Real.log (x : ℝ)) ^ (50 : ℝ)‖ ≤
      1 * ‖Real.log (x : ℝ) ^ ε‖ at hgrowthX
    have heq : Real.log (Real.log (x : ℝ)) ^ (50 : ℝ) =
        Real.log (Real.log (x : ℝ)) ^ (50 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [heq] at hgrowthX
    have hAbs : |iteratedLog x ^ (50 : ℕ)| ≤ Real.log x ^ ε := by
      simpa only [iteratedLog, Real.norm_eq_abs,
        abs_of_pos hrightPos, one_mul] using hgrowthX
    exact (le_abs_self _).trans hAbs
  have hlogPos : 0 < Real.log x := zero_lt_one.trans hlogX
  have hratio :
      iteratedLog x ^ (50 : ℕ) / Real.log x ≤
        Real.log x ^ ε / Real.log x :=
    div_le_div_of_nonneg_right hiterPow hlogPos.le
  have hid :
      Real.log x ^ ε / Real.log x =
        1 / Real.log x ^ (1 - ε) := by
    rw [Real.rpow_sub hlogPos, Real.rpow_one]
    field_simp [hlogPos.ne',
      (Real.rpow_pos_of_pos hlogPos ε).ne']
  change taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x ≤
    K / Real.log x ^ (1 - ε)
  calc
    taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x ≤
        K * (iteratedLog x ^ (50 : ℕ) / Real.log x) := by
      simpa only [K] using henvelope
    _ ≤ K * (Real.log x ^ ε / Real.log x) :=
      mul_le_mul_of_nonneg_left hratio hK
    _ = K / Real.log x ^ (1 - ε) := by simp [hid, div_eq_mul_inv]

theorem taoPrimeTupleSlowScaleWeightedCountBound_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ}
    (hcount : TaoPrimeTupleSlowScaleWeightedCountBound hC hburgess q x R)
    (hprod :
      (∏ j, ((taoDyadicPrimeBand
          (taoPrimeTupleDyadicScales R j)).card : ℝ)) ≤
        8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :
    (taoPrimeTupleTypicalDyadicLengthWeight (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  let A : ℝ :=
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
      (psiNat
        (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
        (taoPrimeTupleRemainderSmoothnessCutoff
          (taoPrimeTupleDyadicScales R)) : ℝ) *
      (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ))
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  calc
    (taoPrimeTupleTypicalDyadicLengthWeight (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
      ((badIntervalTypicalDyadicExponents x).card : ℝ) *
        (psiNat
          (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
          (taoPrimeTupleRemainderSmoothnessCutoff
            (taoPrimeTupleDyadicScales R)) : ℝ) *
        ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      simpa only [TaoPrimeTupleSlowScaleWeightedCountBound,
        taoPrimeTupleDyadicScales] using hcount
    _ = A * (∏ j, ((taoDyadicPrimeBand
        (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      dsimp only [A]
      ring
    _ ≤ A * (8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod hAnonneg
    _ = taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [card_taoPrimeTupleEnlargedRemainderPairs, Nat.cast_mul,
        Nat.cast_prod]
      unfold taoPrimeTupleTypicalWeightedAssemblyFactor A
      rw [mul_div_assoc]
      ac_rfl

theorem eventually_forall_taoPrimeTupleSlowOrderedScaleWeight_le_assembly
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleTypicalDyadicLengthWeight (taoPrimeTupleDyadicScales R) x
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
          taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
            ((taoPrimeTupleEnlargedRemainderPairs
              (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleSlowOrderedScaleWeightedCountBound_of_explicitBurgess hC hburgess hq,
     eventually_forall_taoPrimeTuple_originalBandProduct_le_enlargedBandProduct q]
      with x hcount hprod R hR
  apply taoPrimeTupleSlowScaleWeightedCountBound_le_assemblyFactor_mul_enlarged
    hC hburgess (hcount R hR)
  exact hprod R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

def taoPrimeTupleGlobalTypicalDyadicLengthWeight (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ a ∈ taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x,
    2 ^ a.2.1

theorem taoPrimeTupleGlobalTypicalDyadicLengthWeight_eq_sum (q : ℕ → ℕ) (x : ℕ) :
    taoPrimeTupleGlobalTypicalDyadicLengthWeight q x =
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        taoPrimeTupleTypicalDyadicLengthWeight (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) := by
  rw [taoPrimeTupleGlobalTypicalDyadicLengthWeight,
    taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro R hR
  rfl

theorem eventually_taoPrimeTupleGlobalTypicalLengthWeight_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleSlowOrderedScaleWeight_le_assembly
      hC hburgess hq] with x hx
  rw [taoPrimeTupleGlobalTypicalDyadicLengthWeight_eq_sum, Nat.cast_sum,
    card_taoPrimeTupleGlobalEnlargedRemainderPairs, Nat.cast_sum]
  calc
    (∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleTypicalDyadicLengthWeight (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) : ℝ)) ≤
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleEnlargedRemainderPairs
            (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      exact Finset.sum_le_sum fun R hR => hx R hR
    _ = taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
          ((taoPrimeTupleEnlargedRemainderPairs
            (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [Finset.mul_sum]

theorem eventually_taoPrimeTupleGlobalTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
  filter_upwards
    [eventually_taoPrimeTupleGlobalTypicalLengthWeight_le_assemblyFactor_mul_enlarged
      hC hburgess hq,
     (tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop 2)] with x hweight hlower
  calc
    (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) :=
      hweight
    _ ≤ taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _
        (taoPrimeTupleTypicalWeightedAssemblyFactor_nonneg hC hburgess x)
      exact_mod_cast
        card_taoPrimeTupleGlobalEnlargedRemainderPairs_le_badOneTermCount_mul
          hlower

theorem taoPrimeTupleGlobalTypicalLengthWeight_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ => (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ)) =o[atTop]
      (fun x : ℕ =>
        (badOneTermCount
          (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  let M : ℝ := (1000 : ℝ) ^ (1000 : ℕ)
  have hMpos : 0 < M := by
    exact pow_pos (by norm_num) 1000
  have hsmall := (tendsto_taoPrimeTupleTypicalWeightedAssemblyFactor_zero
    hC hburgess).eventually (Iio_mem_nhds (div_pos hε hMpos))
  filter_upwards
    [eventually_taoPrimeTupleGlobalTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
      hC hburgess hq, hsmall] with x hbound hfactor
  have hfactorM :
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x * M ≤ ε :=
    (le_div_iff₀ hMpos).mp hfactor.le
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ taoPrimeTupleGlobalTypicalDyadicLengthWeight q x),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))]
  calc
    (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := hbound
    _ = (taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x * M) *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      change taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((badOneTermCount
          (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) * M) = _
      ac_rfl
    _ ≤ ε *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) :=
      mul_le_mul_of_nonneg_right hfactorM (by positivity)

end

end Tao2026
