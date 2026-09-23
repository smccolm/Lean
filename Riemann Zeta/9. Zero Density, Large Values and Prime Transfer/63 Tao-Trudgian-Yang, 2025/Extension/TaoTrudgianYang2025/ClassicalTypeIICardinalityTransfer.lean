import TaoTrudgianYang2025.ClassicalTypeIIEnergyTransfer
import TaoTrudgianYang2025.ClassicalTypeIICardinalityPatterns
import TaoTrudgianYang2025.LargeValueUniformity

/-!
# Uniform actual Type-II source cardinality

The source cutoff, dyadic label, mollifier coefficient majorant, threshold
normalization and expanded physical height all retain their original meanings.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeII_uniform_source_class_cardinality_bound
    (σ B a b : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 / (a + b)) (2 / b),
      IsLargeValueBound σ τ (B * τ)) :
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
              (Fintype.card (EnergyColorFiber
                  (classicalSeparatedBranchScaleColor s T Y
                    shiftedZero baseColor L hlocal) label) : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  have hab : 0 < a + b := add_pos ha hb
  have hinv : 1 / (b / 2) = 2 / b := by rw [div_div_eq_mul_div]; ring
  have hlu : 1 / (a + b) ≤ 2 / b := by
    rw [← hinv]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    largeValueBound_uniform_near_logScale_interval σ B
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
  obtain ⟨P, hPN, _hPscale, hPT, hPV, hPcard⟩ :=
    exists_classicalTypeIIClassCardinalityPattern θ s T D (δ / 4) K Y X L
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
  have hcard := hbound P (by rw [hPN]; exact hCevent.trans hNL) hPnear hPthreshold
  rw [hPcard, hPN] at hcard
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  calc
    _ ≤ C * P.T ^ B * (N : ℝ) ^ (ε / (a + b)) := hcard
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
