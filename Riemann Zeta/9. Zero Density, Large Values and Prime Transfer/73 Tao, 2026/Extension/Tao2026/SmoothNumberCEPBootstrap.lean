import Tao2026.SmoothNumberCEPPrimeMass

/-!
# The CEP packet at the smooth-number saddle

This file connects the source parameter `u = log X / log y` to the canonical
CEP cutoff `floor (X^(1/u))`.  In particular, the real endpoint is exactly
`y`, so the natural cutoff used by the source packet is the original
smoothness bound, without an approximation or rounding loss.
-/

namespace Tao2026

noncomputable section

open Filter Topology

/-- At the smooth-number saddle `u = log X / log y`, the canonical CEP real
cutoff `X^(1/u)` is exactly `y`. -/
theorem rpow_one_div_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (X : ℝ) ^ (1 / smoothRankinRatio X y) = y := by
  have hXPos : (0 : ℝ) < X := by positivity
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogXNe : Real.log (X : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hX))).ne'
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [Real.rpow_def_of_pos hXPos, smoothRankinRatio]
  have hexp :
      Real.log (X : ℝ) * (1 / (Real.log (X : ℝ) / Real.log (y : ℝ))) =
        Real.log (y : ℝ) := by
    field_simp
  rw [hexp, Real.exp_log hyPos]

/-- The dual saddle identity `y^u = X`. -/
theorem rpow_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (y : ℝ) ^ smoothRankinRatio X y = X := by
  have hXPos : (0 : ℝ) < X := by positivity
  have hyPos : (0 : ℝ) < y := by positivity
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [Real.rpow_def_of_pos hyPos, smoothRankinRatio]
  have hexp :
      Real.log (y : ℝ) * (Real.log (X : ℝ) / Real.log (y : ℝ)) =
        Real.log (X : ℝ) := by
    field_simp
  rw [hexp, Real.exp_log hXPos]

/-- Logarithmic form of the saddle identity. -/
theorem smoothRankinRatio_mul_log
    {X y : ℕ} (hy : 2 ≤ y) :
    smoothRankinRatio X y * Real.log (y : ℝ) = Real.log (X : ℝ) := by
  have hlogYNe : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hy))).ne'
  rw [smoothRankinRatio]
  field_simp

/-- Consequently, the canonical natural CEP cutoff at the Rankin ratio is
literally the original natural smoothness bound. -/
theorem cepSourceSmoothCutoff_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    cepSourceSmoothCutoff (X : ℝ) (smoothRankinRatio X y) = y := by
  rw [cepSourceSmoothCutoff, rpow_one_div_smoothRankinRatio hX hy,
    Nat.floor_natCast]

/-- Rankin-saddle form of every source lower endpoint, now written as a
power of the original smoothness cutoff `y`. -/
theorem cepSourceBandLower_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℕ) :
    cepSourceBandLower (X : ℝ) (smoothRankinRatio X y) t =
      (y : ℝ) ^
        (1 - ((t + 1 : ℕ) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3) := by
  rw [cepSourceBandLower, cepSourceBandLowerExponent,
    Real.rpow_mul (by positivity : (0 : ℝ) ≤ X),
    rpow_one_div_smoothRankinRatio hX hy]

/-- Rankin-saddle form of every source upper endpoint. -/
theorem cepSourceBandUpper_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℕ) :
    cepSourceBandUpper (X : ℝ) (smoothRankinRatio X y) t =
      (y : ℝ) ^
        (1 - (t : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3) := by
  rw [cepSourceBandUpper, cepSourceBandUpperExponent,
    Real.rpow_mul (by positivity : (0 : ℝ) ≤ X),
    rpow_one_div_smoothRankinRatio hX hy]

/-- The exact source cofactor cutoff at the Rankin saddle. -/
theorem cepSourceCofactorCutoff_smoothRankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y)) :
    cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y) =
      ⌊(y : ℝ) ^
        (1 - (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3)⌋₊ := by
  rw [cepSourceCofactorCutoff,
    cepSourceBandLower_smoothRankinRatio hX hy]
  have hindex :
      cepSourceBandCount (smoothRankinRatio X y) - 1 + 1 =
        cepSourceBandCount (smoothRankinRatio X y) := by omega
  rw [hindex]

/-- Once the band-depth correction is at most one half, every natural
threshold below `sqrt y` lies below the exact source cofactor cutoff. -/
theorem nat_le_cepSourceCofactorCutoff_smoothRankinRatio
    {B X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hdepth :
      (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3 ≤ 1 / 2)
    (hB : (B : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ)) :
    B ≤ cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y) := by
  rw [cepSourceCofactorCutoff_smoothRankinRatio hX hy hk]
  apply (Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).2
  exact hB.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ y by omega)) (by linarith))

/-- Flooring loses at most a factor two once the real input is at least two. -/
theorem half_le_natFloor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one a
  push_cast at hfloor
  linarith

/-- Elementary fourth-root comparison used to absorb the floor loss. -/
theorem two_mul_rpow_quarter_le_rpow_half
    {y : ℕ} (hy : 16 ≤ y) :
    2 * (y : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) := by
  let t := (y : ℝ) ^ (1 / 4 : ℝ)
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have ht0 : 0 ≤ t := Real.rpow_nonneg hy0 _
  have htFour : t ^ (4 : ℕ) = (y : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]
    norm_num
  have htTwo : 2 ≤ t := by
    by_contra hnot
    have htlt : t < 2 := lt_of_not_ge hnot
    have hpow := pow_lt_pow_left₀ htlt ht0 (by norm_num : (4 : ℕ) ≠ 0)
    rw [htFour] at hpow
    norm_num at hpow
    exact (not_lt_of_ge (by exact_mod_cast hy)) hpow
  have htSq : t ^ (2 : ℕ) = (y : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]
    norm_num
  rw [← htSq]
  nlinarith [sq_nonneg (t - 2)]

/-- Quarter-log lower bound for the exact floored cofactor cutoff.  The
geometric hypothesis is an elementary large-`y` condition separated from the
CEP depth correction. -/
theorem quarter_log_y_le_log_cepSourceCofactorCutoff
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hdepth :
      (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3 ≤ 1 / 2)
    (hquarter : 2 * (y : ℝ) ^ (1 / 4 : ℝ) ≤
      (y : ℝ) ^ (1 / 2 : ℝ)) :
    (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (cepSourceCofactorCutoff (X : ℝ)
        (smoothRankinRatio X y) : ℕ) := by
  let u := smoothRankinRatio X y
  let k := cepSourceBandCount u
  let a := (y : ℝ) ^ (1 - (k : ℝ) / Real.log u ^ 3)
  have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have hhalfEndpoint : (y : ℝ) ^ (1 / 2 : ℝ) ≤ a := by
    dsimp only [a]
    exact Real.rpow_le_rpow_of_exponent_le hyOne (by
      simpa only [u, k] using (show (1 / 2 : ℝ) ≤
        1 - (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3 by linarith))
  have hyQuarterOne : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hyOne (by norm_num)
  have haTwo : 2 ≤ a := by
    exact le_trans (by nlinarith [hyQuarterOne]) hhalfEndpoint
  have haFloor : a / 2 ≤ (⌊a⌋₊ : ℝ) := half_le_natFloor haTwo
  have hquarterFloor : (y : ℝ) ^ (1 / 4 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
    have hquarterHalf : (y : ℝ) ^ (1 / 4 : ℝ) ≤ a / 2 := by
      linarith [hquarter, hhalfEndpoint]
    exact hquarterHalf.trans haFloor
  have hquarterPos : 0 < (y : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hfloorPos : (0 : ℝ) < ⌊a⌋₊ := hquarterPos.trans_le hquarterFloor
  have hlogs := Real.strictMonoOn_log.monotoneOn
    hquarterPos hfloorPos hquarterFloor
  rw [Real.log_rpow (by positivity : (0 : ℝ) < y)] at hlogs
  simpa only [cepSourceCofactorCutoff_smoothRankinRatio hX hy hk, u, k, a]
    using hlogs

theorem quarter_log_y_le_log_cepSourceCofactorCutoff_of_sixteen
    {X y : ℕ} (hX : 2 ≤ X) (hy : 16 ≤ y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hdepth :
      (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
          Real.log (smoothRankinRatio X y) ^ 3 ≤ 1 / 2) :
    (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (cepSourceCofactorCutoff (X : ℝ)
        (smoothRankinRatio X y) : ℕ) := by
  exact quarter_log_y_le_log_cepSourceCofactorCutoff hX (by omega) hk hdepth
    (two_mul_rpow_quarter_le_rpow_half hy)

/-- The source correction `k/log(u)^3` is eventually at most one half. -/
theorem eventually_cepSourceBandCount_div_log_cube_le_half :
    ∀ᶠ u : ℝ in atTop,
      (cepSourceBandCount u : ℝ) / Real.log u ^ 3 ≤ 1 / 2 := by
  have hratio : Tendsto (fun u : ℝ =>
      Real.log (Real.log u) / Real.log u) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      Real.tendsto_log_atTop
    simpa [Function.id_def] using h
  have hsmall := hratio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hsmall, hlog, hloglog] with u hsmall hlog hloglog
  have hraw0 : 0 ≤ Real.log u ^ 2 * Real.log (Real.log u) :=
    mul_nonneg (sq_nonneg _) hloglog
  have hfloor : (cepSourceBandCount u : ℝ) ≤
      Real.log u ^ 2 * Real.log (Real.log u) := by
    exact_mod_cast Nat.floor_le hraw0
  have hden : 0 ≤ Real.log u ^ 3 := by positivity
  calc
    (cepSourceBandCount u : ℝ) / Real.log u ^ 3 ≤
        (Real.log u ^ 2 * Real.log (Real.log u)) /
          Real.log u ^ 3 := div_le_div_of_nonneg_right hfloor hden
    _ = Real.log (Real.log u) / Real.log u := by
      have hlogNe : Real.log u ≠ 0 := by linarith
      field_simp
    _ ≤ 1 / 2 := hsmall.le

/-- The source has at least one band for all sufficiently large `u`. -/
theorem eventually_pos_cepSourceBandCount :
    ∀ᶠ u : ℝ in atTop, 0 < cepSourceBandCount u := by
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog, hloglog] with u hlog hloglog
  change 1 ≤ Real.log (Real.log u) at hloglog
  rw [cepSourceBandCount, Nat.floor_pos]
  nlinarith [sq_nonneg (Real.log u)]

/-- A fixed natural threshold (in particular the pinned-PNT threshold) lies
below the source cofactor cutoff throughout the sufficiently large uniform
CEP range `u ≤ sqrt y`. -/
theorem exists_uniform_cepSourceCofactorThreshold (B : ℕ) :
    ∃ U : ℝ, 2 ≤ U ∧
      ∀ X y : ℕ, 2 ≤ X → 2 ≤ y →
        U ≤ smoothRankinRatio X y →
        smoothRankinRatio X y ≤ (y : ℝ) ^ (1 / 2 : ℝ) →
        0 < cepSourceBandCount (smoothRankinRatio X y) ∧
        (cepSourceBandCount (smoothRankinRatio X y) : ℝ) /
            Real.log (smoothRankinRatio X y) ^ 3 ≤ 1 / 2 ∧
        B ≤ cepSourceCofactorCutoff (X : ℝ)
          (smoothRankinRatio X y) := by
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.1
    (eventually_pos_cepSourceBandCount.and
      eventually_cepSourceBandCount_div_log_cube_le_half)
  refine ⟨max (max U₀ (B : ℝ)) 2, le_max_right _ _, ?_⟩
  intro X y hX hy huLower huUpper
  have hU₀u : U₀ ≤ smoothRankinRatio X y :=
    (le_max_left U₀ (B : ℝ)).trans
      ((le_max_left (max U₀ (B : ℝ)) 2).trans huLower)
  obtain ⟨hk, hdepth⟩ := hU₀ _ hU₀u
  refine ⟨hk, hdepth, ?_⟩
  apply nat_le_cepSourceCofactorCutoff_smoothRankinRatio
    hX hy hk hdepth
  exact ((le_max_right U₀ (B : ℝ)).trans
      ((le_max_left (max U₀ (B : ℝ)) 2).trans huLower)).trans huUpper

/-- Every multiplier generated by the exact source packet at the saddle is
at most the ambient `X`. -/
theorem cepSourcePacketProduct_le_X
    {X y m : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hm : m ∈ cepSourcePacketProducts (X : ℝ)
      (smoothRankinRatio X y) y) :
    m ≤ X := by
  rw [cepSourcePacketProducts, cepMultiscalePacketProducts,
    Finset.mem_image] at hm
  obtain ⟨f, hf, rfl⟩ := hm
  have hpacket := cepMultiscalePacketValue_le_pow_sum hf
  have hsum := (sum_cepSourceBandMultiplicity_bounds hu hk).2
  have hbase : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have hreal :
      (cepMultiscalePacketValue
          (Finset.range (cepSourceBandCount (smoothRankinRatio X y))) f : ℝ) ≤
        (X : ℝ) := by
    calc
      (cepMultiscalePacketValue
          (Finset.range (cepSourceBandCount (smoothRankinRatio X y))) f : ℝ) ≤
          ((y ^ ∑ j ∈ Finset.range
            (cepSourceBandCount (smoothRankinRatio X y)),
              cepSourceBandMultiplicity (smoothRankinRatio X y) j : ℕ) : ℝ) := by
        exact_mod_cast hpacket
      _ = (y : ℝ) ^
          ((∑ j ∈ Finset.range
            (cepSourceBandCount (smoothRankinRatio X y)),
              cepSourceBandMultiplicity (smoothRankinRatio X y) j : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.rpow_natCast]
      _ ≤ (y : ℝ) ^ smoothRankinRatio X y := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        exact_mod_cast hsum
      _ = (X : ℝ) := rpow_smoothRankinRatio hX hy
  exact_mod_cast hreal

/-- Source packet products are positive. -/
theorem cepSourcePacketProduct_pos
    {X y m : ℕ} (hX : 2 ≤ X)
    (hm : m ∈ cepSourcePacketProducts (X : ℝ)
      (smoothRankinRatio X y) y) :
    0 < m := by
  have hlower := rpow_cepSourceMultiplierLowerExponent_le_cast
    (x := (X : ℝ)) (u := smoothRankinRatio X y) (y := y)
    (m := m) (by positivity) hm
  have hmReal : (0 : ℝ) < m :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < X) _).trans_le hlower
  exact_mod_cast hmReal

/-- Real division by a positive natural lies below the successor of natural
division. -/
theorem natCast_div_lt_natDiv_add_one
    {X m : ℕ} (hm : 0 < m) :
    (X : ℝ) / (m : ℝ) < (X / m : ℕ) + 1 := by
  have hnat : X < (X / m + 1) * m :=
    (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self (X / m))
  have hreal : (X : ℝ) < ((X / m + 1) * m : ℕ) := by
    exact_mod_cast hnat
  rw [div_lt_iff₀ (by exact_mod_cast hm)]
  push_cast at hreal ⊢
  exact hreal

/-- For a positive packet multiplier below `X`, the real quotient is at most
twice the corresponding natural quotient. -/
theorem cast_div_le_two_mul_natDiv
    {X m : ℕ} (hm : 0 < m) (hmX : m ≤ X) :
    (X : ℝ) / (m : ℝ) ≤ 2 * (X / m : ℕ) := by
  have hq : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm).2 (by simpa using hmX)
  calc
    (X : ℝ) / (m : ℝ) ≤ (X / m : ℕ) + 1 :=
      (natCast_div_lt_natDiv_add_one hm).le
    _ ≤ 2 * (X / m : ℕ) := by exact_mod_cast (show X / m + 1 ≤ 2 * (X / m) by omega)

/-- Explicit endpoint-refined Hildebrand denominator for a cofactor. -/
def cepCofactorHildebrandDenominator (B q w : ℕ) : ℝ :=
  (B : ℝ) * 2 ^ smoothLowerDepth q w *
    Real.log q ^ (smoothLowerDepth q w + 1)

theorem cepCofactorHildebrandDenominator_pos
    {B q w : ℕ} (hB : 0 < B) (hq : 2 ≤ q) :
    0 < cepCofactorHildebrandDenominator B q w := by
  unfold cepCofactorHildebrandDenominator
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  positivity

/-- Coarse upper budget for the integral smoothness depth of source
cofactors. -/
def cepSourceCofactorDepthBudget (u : ℝ) : ℝ :=
  4 * ((cepSourceBandCount u : ℝ) +
    u * (cepSourceBandCount u : ℝ) / Real.log u ^ 3)

/-- A single explicit denominator dominating the endpoint Hildebrand
denominator of every source cofactor once its depth is within the preceding
budget. -/
def cepSourceCofactorDenominatorBudget (B X : ℕ) (u : ℝ) : ℝ :=
  (B : ℝ) * 2 ^ ⌈cepSourceCofactorDepthBudget u⌉₊ *
    Real.log X ^ (⌈cepSourceCofactorDepthBudget u⌉₊ + 1)

/-- The multiplier lower-size ledger bounds the integral Hildebrand depth of
every source cofactor.  A quarter-log lower bound for the floored cofactor
cutoff is the only rounding hypothesis. -/
theorem smoothLowerDepth_cepSourceCofactor_le_budget
    {X y m : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hm : m ∈ cepSourcePacketProducts (X : ℝ)
      (smoothRankinRatio X y) y)
    (hwTwo : 2 ≤ cepSourceCofactorCutoff (X : ℝ)
      (smoothRankinRatio X y))
    (hlogw : (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (cepSourceCofactorCutoff (X : ℝ)
        (smoothRankinRatio X y) : ℕ)) :
    (smoothLowerDepth (X / m)
        (cepSourceCofactorCutoff (X : ℝ)
          (smoothRankinRatio X y)) : ℝ) ≤
      cepSourceCofactorDepthBudget (smoothRankinRatio X y) := by
  let u := smoothRankinRatio X y
  let k := cepSourceBandCount u
  let w := cepSourceCofactorCutoff (X : ℝ) u
  let q := X / m
  have hmPos : 0 < m := cepSourcePacketProduct_pos hX hm
  have hmX : m ≤ X := cepSourcePacketProduct_le_X hX hy hu hk hm
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmRealPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hquotPos : (0 : ℝ) < (X : ℝ) / (m : ℝ) := by positivity
  have hqCast : (q : ℝ) ≤ (X : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmRealPos).2
    have hnat := Nat.div_mul_le_self X m
    exact_mod_cast hnat
  have hlogq : Real.log (q : ℝ) ≤
      Real.log (X : ℝ) - Real.log (m : ℝ) := by
    calc
      Real.log (q : ℝ) ≤ Real.log ((X : ℝ) / (m : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hqPos hquotPos hqCast
      _ = Real.log (X : ℝ) - Real.log (m : ℝ) :=
        Real.log_div (by positivity) (by positivity)
  have hxReal : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hmLower := rpow_cepSourceCoarseLowerExponent_le_cast
    hxReal hu hk hm
  have hmCastPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hlogm :
      (1 - (k : ℝ) / u - (k : ℝ) / Real.log u ^ 3) *
          Real.log (X : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < X) _) hmLower
    rw [Real.log_rpow (by positivity : (0 : ℝ) < X)] at h
    simpa only [u, k] using h
  have hlogqLoss : Real.log (q : ℝ) ≤
      ((k : ℝ) / u + (k : ℝ) / Real.log u ^ 3) *
        Real.log (X : ℝ) := by
    linarith
  have huPos : 0 < u := lt_trans zero_lt_one hu
  have hlogyPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : Real.log (X : ℝ) = u * Real.log (y : ℝ) := by
    simpa only [u] using (smoothRankinRatio_mul_log hy).symm
  have hlogqBudget : Real.log (q : ℝ) ≤
      ((k : ℝ) + u * (k : ℝ) / Real.log u ^ 3) *
        Real.log (y : ℝ) := by
    rw [hlogX] at hlogqLoss
    convert hlogqLoss using 1
    field_simp [huPos.ne']
  have hbudget0 : 0 ≤ (k : ℝ) + u * (k : ℝ) / Real.log u ^ 3 := by
    have hlogu : 0 < Real.log u := Real.log_pos hu
    positivity
  have hlogwPos : 0 < Real.log (w : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < w by simpa only [w] using hwTwo))
  have hlogyFour : Real.log (y : ℝ) ≤ 4 * Real.log (w : ℝ) := by
    have : (1 / 4 : ℝ) * Real.log (y : ℝ) ≤ Real.log (w : ℝ) := by
      simpa only [w, u] using hlogw
    linarith
  have hratio : smoothRankinRatio q w ≤
      4 * ((k : ℝ) + u * (k : ℝ) / Real.log u ^ 3) := by
    rw [smoothRankinRatio, div_le_iff₀ hlogwPos]
    calc
      Real.log (q : ℝ) ≤
          ((k : ℝ) + u * (k : ℝ) / Real.log u ^ 3) *
            Real.log (y : ℝ) := hlogqBudget
      _ ≤ ((k : ℝ) + u * (k : ℝ) / Real.log u ^ 3) *
          (4 * Real.log (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogyFour hbudget0
      _ = (4 * ((k : ℝ) + u * (k : ℝ) / Real.log u ^ 3)) *
          Real.log (w : ℝ) := by ring
  exact (smoothLowerDepth_cast_le_rankinRatio (by omega) (by simpa only [w] using hwTwo)).trans
    (by simpa only [cepSourceCofactorDepthBudget, u, k, w, q] using hratio)

/-- The pointwise cofactor denominator is bounded by the common source
budget. -/
theorem cepCofactorHildebrandDenominator_le_sourceBudget
    {B X y m : ℕ} (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hm : m ∈ cepSourcePacketProducts (X : ℝ)
      (smoothRankinRatio X y) y)
    (hwTwo : 2 ≤ cepSourceCofactorCutoff (X : ℝ)
      (smoothRankinRatio X y))
    (hlogw : (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (cepSourceCofactorCutoff (X : ℝ)
        (smoothRankinRatio X y) : ℕ)) :
    cepCofactorHildebrandDenominator B (X / m)
        (cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y)) ≤
      cepSourceCofactorDenominatorBudget B X (smoothRankinRatio X y) := by
  let u := smoothRankinRatio X y
  let w := cepSourceCofactorCutoff (X : ℝ) u
  let q := X / m
  let d := smoothLowerDepth q w
  let K := ⌈cepSourceCofactorDepthBudget u⌉₊
  have hmPos : 0 < m := cepSourcePacketProduct_pos (by omega) hm
  have hmX : m ≤ X := cepSourcePacketProduct_le_X (by omega) hy hu hk hm
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hdepth : (d : ℝ) ≤ cepSourceCofactorDepthBudget u := by
    simpa only [d, q, w, u] using
      smoothLowerDepth_cepSourceCofactor_le_budget
        (by omega) hy hu hk hm hwTwo hlogw
  have hdepthCeil : (d : ℝ) ≤ (K : ℝ) :=
    hdepth.trans (by simpa only [K] using
      (Nat.le_ceil (cepSourceCofactorDepthBudget u)))
  have hdK : d ≤ K := by exact_mod_cast hdepthCeil
  have hqX : q ≤ X := by
    dsimp only [q]
    exact Nat.div_le_self X m
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqOne)
  have hlogqX : Real.log (q : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show (0 : ℝ) < q
      exact_mod_cast (show 0 < q by omega)
    · show (0 : ℝ) < X
      positivity
    · exact_mod_cast hqX
  have hlogXOne : 1 ≤ Real.log (X : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact hthree.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) (by show (0 : ℝ) < X; positivity)
      (by exact_mod_cast hX))
  have htwoPow : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hdK
  have hlogPow : Real.log (q : ℝ) ^ (d + 1) ≤
      Real.log (X : ℝ) ^ (K + 1) := by
    exact (pow_le_pow_left₀ hlogq0 hlogqX (d + 1)).trans
      (pow_le_pow_right₀ hlogXOne (Nat.add_le_add_right hdK 1))
  unfold cepCofactorHildebrandDenominator
  unfold cepSourceCofactorDenominatorBudget
  have hfinal : (B : ℝ) * (2 : ℝ) ^ d * Real.log (q : ℝ) ^ (d + 1) ≤
      (B : ℝ) * (2 : ℝ) ^ K * Real.log (X : ℝ) ^ (K + 1) := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left
        (mul_le_mul htwoPow hlogPow
          (pow_nonneg hlogq0 _) (by positivity))
        (Nat.cast_nonneg B))
  simpa only [u, w, q, d, K] using hfinal

/-- The already-proved endpoint Hildebrand estimate supplies the uniform
cofactor-density premise once its explicit denominator is bounded by
`1/(2D)`. The case of a cofactor below three is absorbed by `4D ≤ 1`. -/
theorem cofactorDensity_of_hildebrandDenominatorBound
    {B X m w : ℕ} {D : ℝ}
    (hB : 4 ≤ B)
    (htheta : ∀ n : ℕ, B ≤ n →
      (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hmPos : 0 < m) (hmX : m ≤ X) (hBw : B ≤ w)
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hden : cepCofactorHildebrandDenominator B (X / m) w ≤
      1 / (2 * D)) :
    D * (X : ℝ) / (m : ℝ) ≤ (psiNat (X / m) w : ℝ) := by
  let q := X / m
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hquot : (X : ℝ) / (m : ℝ) ≤ 2 * (q : ℕ) := by
    simpa only [q] using cast_div_le_two_mul_natDiv hmPos hmX
  by_cases hqThree : 3 ≤ q
  · have hwTwo : 2 ≤ w := (by omega : 2 ≤ B).trans hBw
    have hhilbert :
        (q : ℝ) / cepCofactorHildebrandDenominator B q w ≤
          (psiNat q w : ℝ) := by
      simpa only [cepCofactorHildebrandDenominator] using
        self_div_endpointHildebrandDenominator_le_psiNat
          hB hqThree hwTwo htheta hBw
    have hdenPos : 0 < cepCofactorHildebrandDenominator B q w :=
      cepCofactorHildebrandDenominator_pos (by omega) (by omega)
    have htwoDPos : 0 < 2 * D := mul_pos (by norm_num) hD
    have hdenMul :
        cepCofactorHildebrandDenominator B q w * (2 * D) ≤ 1 := by
      apply (le_div_iff₀ htwoDPos).mp
      simpa only [q] using hden
    apply le_trans ?_ hhilbert
    apply (le_div_iff₀ hdenPos).2
    calc
      (D * (X : ℝ) / (m : ℝ)) *
          cepCofactorHildebrandDenominator B q w ≤
        (D * (2 * (q : ℕ))) *
          cepCofactorHildebrandDenominator B q w := by
        apply mul_le_mul_of_nonneg_right
        · simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hquot hD.le
        · exact hdenPos.le
      _ = (cepCofactorHildebrandDenominator B q w * (2 * D)) * q := by
        ring
      _ ≤ 1 * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hdenMul (Nat.cast_nonneg q)
      _ = (q : ℝ) := one_mul _
  · have hqTwo : q ≤ 2 := by omega
    have hpsi : (1 : ℝ) ≤ psiNat q w := by
      exact_mod_cast one_le_psiNat hqOne
    calc
      D * (X : ℝ) / (m : ℝ) ≤ D * (2 * (q : ℕ)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hquot hD.le
      _ ≤ D * 4 := by
        gcongr
        have hqTwoReal : (q : ℝ) ≤ 2 := by exact_mod_cast hqTwo
        linarith
      _ = 4 * D := by ring
      _ ≤ 1 := hDsmall
      _ ≤ (psiNat q w : ℝ) := hpsi

theorem cepSourceCofactorDensity_of_hildebrandDenominatorBound
    {B X y m : ℕ} {D : ℝ}
    (hB : 4 ≤ B)
    (htheta : ∀ n : ℕ, B ≤ n →
      (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hm : m ∈ cepSourcePacketProducts (X : ℝ)
      (smoothRankinRatio X y) y)
    (hBw : B ≤ cepSourceCofactorCutoff (X : ℝ)
      (smoothRankinRatio X y))
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hden : cepCofactorHildebrandDenominator B (X / m)
        (cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y)) ≤
      1 / (2 * D)) :
    D * (X : ℝ) / (m : ℝ) ≤
      (psiNat (X / m)
        (cepSourceCofactorCutoff (X : ℝ)
          (smoothRankinRatio X y)) : ℝ) := by
  let q := X / m
  let w := cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y)
  have hmPos : 0 < m := cepSourcePacketProduct_pos hX hm
  have hmX : m ≤ X := cepSourcePacketProduct_le_X hX hy hu hk hm
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hquot : (X : ℝ) / (m : ℝ) ≤ 2 * (q : ℕ) := by
    simpa only [q] using cast_div_le_two_mul_natDiv hmPos hmX
  by_cases hqThree : 3 ≤ q
  · have hwTwo : 2 ≤ w := (by omega : 2 ≤ B).trans hBw
    have hhilbert :
        (q : ℝ) / cepCofactorHildebrandDenominator B q w ≤
          (psiNat q w : ℝ) := by
      simpa only [cepCofactorHildebrandDenominator] using
        self_div_endpointHildebrandDenominator_le_psiNat
          hB hqThree hwTwo htheta hBw
    have hdenPos : 0 < cepCofactorHildebrandDenominator B q w :=
      cepCofactorHildebrandDenominator_pos (by omega) (by omega)
    have htwoDPos : 0 < 2 * D := mul_pos (by norm_num) hD
    have hdenMul :
        cepCofactorHildebrandDenominator B q w * (2 * D) ≤ 1 := by
      apply (le_div_iff₀ htwoDPos).mp
      simpa only [q, w] using hden
    apply le_trans ?_ hhilbert
    apply (le_div_iff₀ hdenPos).2
    calc
      (D * (X : ℝ) / (m : ℝ)) *
          cepCofactorHildebrandDenominator B q w ≤
        (D * (2 * (q : ℕ))) *
          cepCofactorHildebrandDenominator B q w := by
        apply mul_le_mul_of_nonneg_right
        · simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hquot hD.le
        · exact hdenPos.le
      _ = (cepCofactorHildebrandDenominator B q w * (2 * D)) * q := by
        ring
      _ ≤ 1 * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hdenMul (Nat.cast_nonneg q)
      _ = (q : ℝ) := one_mul _
  · have hqTwo : q ≤ 2 := by omega
    have hpsi : (1 : ℝ) ≤ psiNat q w := by
      exact_mod_cast one_le_psiNat hqOne
    calc
      D * (X : ℝ) / (m : ℝ) ≤ D * (2 * (q : ℕ)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hquot hD.le
      _ ≤ D * 4 := by
        gcongr
        have hqTwoReal : (q : ℝ) ≤ 2 := by exact_mod_cast hqTwo
        linarith
      _ = 4 * D := by ring
      _ ≤ 1 := hDsmall
      _ ≤ (psiNat q w : ℝ) := hpsi

/-- At the Rankin saddle, the canonical source packet feeds directly into
`psiNat X y`: the source cutoff has become the original `y`, while the
cofactor cutoff remains the exact floor of the lowest source endpoint. -/
theorem density_mul_X_mul_cepRankinPrimeMassPacket_le_psiNat
    {X y : ℕ} {D E : ℝ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y) (hD0 : 0 ≤ D)
    (hE0 : ∀ j ∈ Finset.range
        (cepSourceBandCount (smoothRankinRatio X y)),
      0 ≤ cepSourcePrimeMassMain (smoothRankinRatio X y) j - E)
    (hMass : HasCEPSourcePrimeMassLower (X : ℝ)
      (smoothRankinRatio X y) y E)
    (hD : ∀ m ∈ cepSourcePacketProducts (X : ℝ)
        (smoothRankinRatio X y) y,
      D * (X : ℝ) / (m : ℝ) ≤
        (psiNat (X / m)
          (cepSourceCofactorCutoff (X : ℝ)
            (smoothRankinRatio X y)) : ℝ)) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range
            (cepSourceBandCount (smoothRankinRatio X y)),
          (cepSourcePrimeMassMain (smoothRankinRatio X y) j - E) ^
              cepSourceBandMultiplicity (smoothRankinRatio X y) j /
            (Nat.factorial
              (cepSourceBandMultiplicity (smoothRankinRatio X y) j) : ℝ) ≤
      (psiNat X y : ℝ) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hcutoff := cepSourceSmoothCutoff_smoothRankinRatio hX hy
  have hMass' : HasCEPSourcePrimeMassLower (X : ℝ)
      (smoothRankinRatio X y)
      (cepSourceSmoothCutoff (X : ℝ) (smoothRankinRatio X y)) E := by
    simpa only [hcutoff] using hMass
  have hD' : ∀ m ∈ cepSourcePacketProducts (X : ℝ)
        (smoothRankinRatio X y)
        (cepSourceSmoothCutoff (X : ℝ) (smoothRankinRatio X y)),
      D * (X : ℝ) / (m : ℝ) ≤
        (psiNat (X / m)
          (cepSourceCofactorCutoff (X : ℝ)
            (smoothRankinRatio X y)) : ℝ) := by
    simpa only [hcutoff] using hD
  have h := density_mul_X_mul_cepCanonicalPrimeMassPacket_le_psiNat
    hD0 hx hu hE0 hMass' hD'
  simpa only [hcutoff] using h

/-- End-to-end finite CEP/Hildebrand bridge.  It combines the exact source
packet, reciprocal-prime mass, the saddle cutoff identity, and the elementary
endpoint Hildebrand lower bound on every cofactor.  Only the displayed common
denominator bound and the bandwise prime-mass estimate remain as scalar and
prime-distribution inputs. -/
theorem cepRankinPrimeMassPacket_le_psiNat_of_hildebrandDenominatorBound
    {B X y : ℕ} {D E : ℝ}
    (hB : 4 ≤ B)
    (htheta : ∀ n : ℕ, B ≤ n →
      (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hBw : B ≤ cepSourceCofactorCutoff (X : ℝ)
      (smoothRankinRatio X y))
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hden : ∀ m ∈ cepSourcePacketProducts (X : ℝ)
        (smoothRankinRatio X y) y,
      cepCofactorHildebrandDenominator B (X / m)
          (cepSourceCofactorCutoff (X : ℝ) (smoothRankinRatio X y)) ≤
        1 / (2 * D))
    (hE0 : ∀ j ∈ Finset.range
        (cepSourceBandCount (smoothRankinRatio X y)),
      0 ≤ cepSourcePrimeMassMain (smoothRankinRatio X y) j - E)
    (hMass : HasCEPSourcePrimeMassLower (X : ℝ)
      (smoothRankinRatio X y) y E) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range
            (cepSourceBandCount (smoothRankinRatio X y)),
          (cepSourcePrimeMassMain (smoothRankinRatio X y) j - E) ^
              cepSourceBandMultiplicity (smoothRankinRatio X y) j /
            (Nat.factorial
              (cepSourceBandMultiplicity (smoothRankinRatio X y) j) : ℝ) ≤
      (psiNat X y : ℝ) := by
  apply density_mul_X_mul_cepRankinPrimeMassPacket_le_psiNat
    hX hy hu hD.le hE0 hMass
  intro m hm
  exact cepSourceCofactorDensity_of_hildebrandDenominatorBound
    hB htheta hX hy hu hk hm hBw hD hDsmall (hden m hm)

/-- Common-budget form of the end-to-end bridge.  The cofactor denominator
is now a single scalar expression depending only on `B`, `X`, and `u`, not on
the packet multiplier. -/
theorem cepRankinPrimeMassPacket_le_psiNat_of_sourceDenominatorBudget
    {B X y : ℕ} {D E : ℝ}
    (hB : 4 ≤ B)
    (htheta : ∀ n : ℕ, B ≤ n →
      (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hk : 0 < cepSourceBandCount (smoothRankinRatio X y))
    (hBw : B ≤ cepSourceCofactorCutoff (X : ℝ)
      (smoothRankinRatio X y))
    (hlogw : (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (cepSourceCofactorCutoff (X : ℝ)
        (smoothRankinRatio X y) : ℕ))
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hden : cepSourceCofactorDenominatorBudget B X
        (smoothRankinRatio X y) ≤ 1 / (2 * D))
    (hE0 : ∀ j ∈ Finset.range
        (cepSourceBandCount (smoothRankinRatio X y)),
      0 ≤ cepSourcePrimeMassMain (smoothRankinRatio X y) j - E)
    (hMass : HasCEPSourcePrimeMassLower (X : ℝ)
      (smoothRankinRatio X y) y E) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range
            (cepSourceBandCount (smoothRankinRatio X y)),
          (cepSourcePrimeMassMain (smoothRankinRatio X y) j - E) ^
              cepSourceBandMultiplicity (smoothRankinRatio X y) j /
            (Nat.factorial
              (cepSourceBandMultiplicity (smoothRankinRatio X y) j) : ℝ) ≤
      (psiNat X y : ℝ) := by
  apply cepRankinPrimeMassPacket_le_psiNat_of_hildebrandDenominatorBound
    hB htheta (by omega) hy hu hk hBw hD hDsmall
  · intro m hm
    exact (cepCofactorHildebrandDenominator_le_sourceBudget
      hX hy hu hk hm (by omega) hlogw).trans hden
  · exact hE0
  · exact hMass

end

end Tao2026
