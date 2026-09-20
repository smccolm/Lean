import TaoTrudgianYang2025.ClassicalTypeIUniformity

/-!
# Uniform Type II energy transfer

The sharp mollifier has a proved divisor majorant. Its normalization and
dyadic-count loss are matched to the general large-value threshold window.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- Exact separation of the scale power from the Type II divisor and
dyadic-count normalization. -/
theorem classicalTypeII_normalized_sourceThreshold_eq
    (Y N : ℕ) (s η C : ℝ) (hY : 1 < Y) (hN : 0 < N) (hC : 0 < C) :
    ((((3 / 4 : ℝ) * (3 / 4)) / Nat.clog 2 Y) /
      (C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-s))) =
      (N : ℝ) ^ (s - η) /
        ((16 / 9 : ℝ) * C * (2 : ℝ) ^ η * Nat.clog 2 Y) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hclog : (0 : ℝ) < Nat.clog 2 Y := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hY
  have hNS := Real.rpow_pos_of_pos hNpos s
  have hNE := Real.rpow_pos_of_pos hNpos η
  have hTwo := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) η
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNpos.le,
    Real.rpow_neg hNpos.le, Real.rpow_sub hNpos]
  field_simp
  ring

/-- The divisor exponent spends half the available threshold window; the
other half absorbs the fixed normalization and source dyadic count. This is
uniform in both the cutoff `Y` and the extracted scale `N`. -/
theorem eventually_classicalTypeII_normalized_sourceThreshold_lower
    (s b ε η C : ℝ) (hb : 0 < b) (hε : 0 < ε) (hη : η ≤ ε / 2)
    (hC : 0 < C) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ Y N : ℕ,
      1 < Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ → T ^ b ≤ (N : ℝ) →
      (N : ℝ) ^ (s - ε) ≤
        ((((3 / 4 : ℝ) * (3 / 4)) / Nat.clog 2 Y) /
          (C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-s))) := by
  let K : ℝ := (16 / 9) * C * (2 : ℝ) ^ η
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow
    K (b * (ε / 2)) hK.le (by positivity),
    Filter.eventually_ge_atTop (2 : ℝ)] with T hclog hT
  intro Y N hY hYA hNL
  have hTpos : 0 < T := by linarith
  have hNreal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) hb).trans_le hNL
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hclogPos : (0 : ℝ) < Nat.clog 2 Y := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hY
  have hdenPos : 0 < K * Nat.clog 2 Y := mul_pos hK hclogPos
  have hden : K * Nat.clog 2 Y ≤ (N : ℝ) ^ (ε - η) := by
    calc
      K * Nat.clog 2 Y ≤ K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.clog_mono_right 2 hYA) hK.le
      _ ≤ T ^ (b * (ε / 2)) := hclog
      _ = (T ^ b) ^ (ε / 2) := Real.rpow_mul hTpos.le _ _
      _ ≤ (N : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hNL (by linarith)
      _ ≤ (N : ℝ) ^ (ε - η) :=
        Real.rpow_le_rpow_of_exponent_le hNreal.le (by linarith)
  rw [classicalTypeII_normalized_sourceThreshold_eq Y N s η C hY hNnat hC]
  have hid : (N : ℝ) ^ (s - ε) =
      (N : ℝ) ^ (s - η) / (N : ℝ) ^ (ε - η) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  rw [hid]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) hdenPos hden

/-- The Type II physical scale window is uniformly close to its compact
limiting interval, including the expanded beta-removal height. -/
theorem eventually_classicalTypeII_logScale_near_interval
    (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N H : ℝ,
      T ^ b ≤ N → N ≤ T ^ a → T ≤ H → H ≤ 3 * T →
      ∃ τ ∈ Set.Icc (1 / a) (1 / b), |Real.logb N H - τ| ≤ δ := by
  have hpow := (tendsto_rpow_atTop (mul_pos hb hδ)).eventually
    (Filter.eventually_ge_atTop (3 : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hpow] with T hT hpower
  intro N H hNL hNU hHL hHU
  have hTpos : 0 < T := by linarith
  have hNone : 1 < N :=
    (Real.one_lt_rpow (by linarith : 1 < T) hb).trans_le hNL
  have hNpos : 0 < N := zero_lt_one.trans hNone
  have hHpos : 0 < H := hTpos.trans_le hHL
  have hNpower : 3 ≤ N ^ δ := by
    calc
      3 ≤ T ^ (b * δ) := hpower
      _ = (T ^ b) ^ δ := Real.rpow_mul hTpos.le b δ
      _ ≤ N ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hNL hδ.le
  have hTupper : T ≤ N ^ (1 / b) := by
    calc
      T = (T ^ b) ^ (1 / b) := by
        rw [← Real.rpow_mul hTpos.le, mul_one_div_cancel hb.ne', Real.rpow_one]
      _ ≤ N ^ (1 / b) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hNL (by positivity)
  have hlogL : 1 / a ≤ Real.logb N H := by
    apply (Real.le_logb_iff_rpow_le hNone hHpos).mpr
    calc
      N ^ (1 / a) ≤ (T ^ a) ^ (1 / a) :=
        Real.rpow_le_rpow hNpos.le hNU (by positivity)
      _ = T := by
        rw [← Real.rpow_mul hTpos.le, mul_one_div_cancel ha.ne', Real.rpow_one]
      _ ≤ H := hHL
  have hlogU : Real.logb N H ≤ 1 / b + δ := by
    apply (Real.logb_le_iff_le_rpow hNone hHpos).mpr
    rw [Real.rpow_add hNpos]
    nlinarith [Real.rpow_pos_of_pos hNpos (1 / b)]
  exact exists_mem_Icc_abs_sub_le_of_bounds (1 / a) (1 / b) (Real.logb N H) δ
    (one_div_le_one_div_of_le hb hba) hδ.le (by linarith) hlogU

/-- The genuine Type II dyadic label gives the upper physical scale bound
for the two floor cutoffs. -/
theorem classicalTypeII_sourceScale_upper
    (T a b : ℝ) (hT : 0 < T)
    (r : Fin (Nat.clog 2 ⌊T ^ a⌋₊)) :
    ((2 ^ (r : ℕ) * ⌊T ^ b⌋₊ : ℕ) : ℝ) ≤ T ^ (a + b) := by
  have hr : (2 ^ (r : ℕ) : ℕ) ≤ ⌊T ^ a⌋₊ :=
    (Nat.pow_lt_of_lt_clog r.2).le
  calc
    ((2 ^ (r : ℕ) * ⌊T ^ b⌋₊ : ℕ) : ℝ) ≤
        (⌊T ^ a⌋₊ : ℝ) * (⌊T ^ b⌋₊ : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right ⌊T ^ b⌋₊ hr
    _ ≤ T ^ a * T ^ b :=
      mul_le_mul (Nat.floor_le (Real.rpow_nonneg hT.le _))
        (Nat.floor_le (Real.rpow_nonneg hT.le _)) (Nat.cast_nonneg _)
          (Real.rpow_nonneg hT.le _)
    _ = T ^ (a + b) := (Real.rpow_add hT _ _).symm

/-- Uniform physical-height energy control for an actual Type II source
fiber. The source cutoffs, dyadic label, divisor coefficient bound, threshold
window, separation, and expanded height window are all consumed here. The
single source real-part window is chosen before that line is fixed. -/
theorem classicalTypeII_uniform_source_class_energy_bound
    (σ B a b : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 / (a + b)) (2 / b),
      IsLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s D θ : ℝ, 0 ≤ s → σ - δ / 2 ≤ s → θ ≤ 1 →
          ∀ᶠ T : ℝ in Filter.atTop,
            let Y := ⌊T ^ a⌋₊
            let X := ⌊T ^ b⌋₊
            ∀ (L : ℕ)
              (shiftedZero : ↥(zerosInRect s 1 T (2 * T)) → ℝ)
              (baseColor : ↥(zerosInRect s 1 T (2 * T)) →
                ClassicalBranchScaleColor T Y)
              (hlocal : ∀ z : ℤ,
                (unitBinFinset (fun x : ClassicalSlabZeroCopy s T =>
                  shiftedZero x.1) z).card ≤ L)
              (label : ClassicalSeparatedBranchScaleColor T Y L)
              (r : Fin (Nat.clog 2 Y)),
              label.1 = some (Sum.inr r) →
              (∀ ρ, T - T ^ θ ≤ shiftedZero ρ ∧
                shiftedZero ρ ≤ 2 * T + T ^ θ) →
              (∀ x : EnergyColorFiber
                (classicalSeparatedBranchScaleColor s T Y
                  shiftedZero baseColor L hlocal) label,
                ClassicalBranchScaleLarge s T D Y X label.1 (shiftedZero x.1.1)) →
              (approximateAdditiveEnergyOf 1
                  (fun x : EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y
                      shiftedZero baseColor L hlocal) label =>
                    shiftedZero x.1.1) : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  have hab : 0 < a + b := add_pos ha hb
  have hinv : 1 / (b / 2) = 2 / b := by rw [div_div_eq_mul_div]; ring
  have hlu : 1 / (a + b) ≤ 2 / b := by
    rw [← hinv]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    largeValueEnergyBound_uniform_near_logScale_interval σ B
      (1 / (a + b)) (2 / b) hB hlu hLV (ε / (a + b)) (div_pos hε hab)
  obtain ⟨K, hK, hcoeff⟩ := sharpMollifiedCoeff_bound (δ / 4) (by linarith)
  let Cfinal : ℝ := max 1 (C * (3 : ℝ) ^ B)
  refine ⟨Cfinal, le_max_left _ _, δ, hδ, ?_⟩
  intro s D θ hs hsσ hθ
  have hthreshold := eventually_classicalTypeII_normalized_sourceThreshold_lower
    s (b / 2) (δ / 2) (δ / 4) K (by linarith) (by linarith) (by linarith) hK
  have hnear := eventually_classicalTypeII_logScale_near_interval
    (a + b) (b / 2) δ hab (by linarith) (by linarith) hδ
  have hCevent := (tendsto_rpow_atTop (by linarith : 0 < b / 2)).eventually
    (Filter.eventually_ge_atTop C)
  obtain ⟨Tcut, hTcut, hcut⟩ := eventually_classical_dichotomy_cutoffs
    a (2 * b) ha (by positivity) (by linarith) haone
  filter_upwards [hthreshold, hnear, hCevent,
    eventually_classicalTypeI_sourceScale_lower b hb,
    Filter.eventually_ge_atTop Tcut] with T hthreshold hnear hCevent hscale hTC
  dsimp only
  intro L shiftedZero baseColor hlocal label r hlabel hW hlarge
  have hT : 8 ≤ T := hTcut.trans hTC
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hcut' := hcut T hTC
  have hcancel : 2 * b / 2 = b := by ring
  dsimp only at hcut'
  rw [hcancel] at hcut'
  let Y := ⌊T ^ a⌋₊
  let X := ⌊T ^ b⌋₊
  let N := 2 ^ (r : ℕ) * X
  have hNL : T ^ (b / 2) ≤ (N : ℝ) := hscale r
  have hNU : (N : ℝ) ≤ T ^ (a + b) := classicalTypeII_sourceScale_upper T a b hTpos r
  have hNreal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) (by linarith : 0 < b / 2)).trans_le hNL
  have hN : 1 < N := by exact_mod_cast hNreal
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1| := by
    intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy s T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal label x y hxy
  obtain ⟨P, hPN, _hPscale, hPT, hPV, hPE⟩ :=
    exists_classicalTypeIIClassPattern θ s T D (δ / 4) K Y X L
      shiftedZero baseColor hlocal label r hlabel hTpos hcut'.2.1 hN hs
        (by linarith) hK (hcoeff Y X) hW hlarge hsep
  have hheight : T ≤ P.T ∧ P.T ≤ 3 * T := by
    rw [hPT]
    have hp : T ^ θ ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hTone hθ
    constructor <;> linarith [Real.rpow_pos_of_pos hTpos θ]
  have hPnear : ∃ τ ∈ Set.Icc (1 / (a + b)) (2 / b),
      |Real.logb P.N P.T - τ| ≤ δ := by
    rw [hPN, ← hinv]
    exact hnear N P.T hNL hNU hheight.1 hheight.2
  have hPthreshold : P.N ^ (σ - δ) ≤ P.V := by
    rw [hPV, hPN]
    exact (Real.rpow_le_rpow_of_exponent_le hNreal.le (by linarith)).trans
      (hthreshold Y N hcut'.2.1 hcut'.2.2.2.1 hNL)
  have henergy := hbound P (by rw [hPN]; exact hCevent.trans hNL) hPnear hPthreshold
  rw [hPE, hPN] at henergy
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  calc
    _ ≤ C * P.T ^ B * (N : ℝ) ^ (ε / (a + b)) := henergy
    _ ≤ C * (3 * T) ^ B * (T ^ (a + b)) ^ (ε / (a + b)) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow P.T_pos.le hheight.2 hB) hCnonneg)
        (Real.rpow_le_rpow hNpos.le hNU (div_pos hε hab).le)
        (Real.rpow_nonneg hNpos.le _) (by positivity)
    _ = (C * (3 : ℝ) ^ B) * T ^ (B + ε) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTpos.le,
        ← Real.rpow_mul hTpos.le, mul_div_cancel₀ ε hab.ne']
      rw [Real.rpow_add hTpos]
      ring
    _ ≤ Cfinal * T ^ (B + ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTpos.le _)

end TaoTrudgianYang2025
