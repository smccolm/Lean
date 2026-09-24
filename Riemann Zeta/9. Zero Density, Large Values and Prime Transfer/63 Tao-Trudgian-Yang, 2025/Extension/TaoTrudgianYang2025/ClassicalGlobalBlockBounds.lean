import TaoTrudgianYang2025.ClassicalGlobalBottomSource
import TaoTrudgianYang2025.ClassicalGlobalDirectSource
import TaoTrudgianYang2025.ClassicalGlobalSourceClassification

/-!
# One parameter window for every occupied global source block

Bottom, reflected and direct estimates use their genuine upstream bounds.
An occupied block is classified at an actual ordinate, with terminal and
small-scale alternatives excluded. All constants are chosen before the
shifted source line. This is a per-block bound, not yet the full zero slab.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalGlobal_uniform_source_block_cardinality_bound
    (σ B a : ℝ) (hσ : 1/2 < σ) (hσOne : σ < 1)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (σ-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (σ-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, σ-eta ≤ s → s ≤ σ → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
                  (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                  (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                  (∀ x,
                    ((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ) ≤
                      ‖typeISourceSmoothBlock ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r s (W x)‖) →
                  (Fintype.card ι : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨CB,hCB,δB,hδB,hBottom⟩ :=
    classicalBottom_uniform_shifted_line_source_cardinality_bound σ B a hB ha hGeneral ε hε
  obtain ⟨etaR,hEtaR,hEtaRGap,dR,hdR,hdRGap,_hdREps,CR,hCR,hReflected⟩ :=
    classicalReflected_uniform_shifted_line_source_cardinality_bound σ B hσ hσOne hB
      (fun τ hτ => hZeta τ hτ.1) ε hε
  obtain ⟨etaD,hEtaD,_hEtaDGap,dD,hdD,_hdDQuarter,_hdDEps,CD,hCD,hDirect⟩ :=
    classicalDirect_uniform_shifted_line_source_cardinality_bound σ B a hσ hB ha haHalf
      (fun τ hτ => hZeta τ hτ.1) ε hε
  let eta := min etaR (min etaD (δB/4))
  have hEta : 0 < eta := by dsimp [eta]; positivity
  have hEtaRLe : eta ≤ etaR := min_le_left _ _
  have hEtaDLe : eta ≤ etaD := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaBLe : eta ≤ δB/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hEtaGap : eta ≤ (σ-1/2)/2 := hEtaRLe.trans hEtaRGap
  let d := min dR (min dD (min (a*δB/8) (ε/100)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdRLe : d ≤ dR := min_le_left _ _
  have hdDLe : d ≤ dD := (min_le_right _ _).trans (min_le_left _ _)
  have hdRest : d ≤ min (a*δB/8) (ε/100) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdB : d ≤ a*δB/8 := hdRest.trans (min_le_left _ _)
  have hdEps : d ≤ ε/100 := hdRest.trans (min_le_right _ _)
  have hdGap : d ≤ (σ-1/2)/2000 := hdRLe.trans hdRGap
  let C := max CB (max CR CD)
  have hC : 1 ≤ C := hCB.trans (le_max_left _ _)
  have hCBLe : CB ≤ C := le_max_left _ _
  have hCRLe : CR ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCDLe : CD ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEps,C,hC,?_⟩
  intro s u hsLower hsUpper hu huD
  have hs : 1/2 < s := by linarith
  have hsOne : s < 1 := hsUpper.trans_lt hσOne
  have hdOne : d ≤ 1 := by linarith
  have hdSourceGap : d ≤ (s-1/2)/1000 := by linarith
  obtain ⟨TR,_hTR,hReflectedT⟩ :=
    hReflected s u (by linarith) hsUpper hu (huD.trans hdRLe)
  obtain ⟨TClass,_hTClass,hClassify⟩ :=
    eventually_large_global_source_classification s d u hs hsOne hd hdSourceGap huD
  filter_upwards [
    hBottom s u d (by linarith) hsOne.le (by linarith) (huD.trans hdB) hdOne,
    hDirect s u (by linarith) hu (huD.trans hdDLe),
    Filter.eventually_ge_atTop TR,Filter.eventually_ge_atTop TClass,
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)]
    with T hBottomT hDirectT hTR hTClass hPower hT
  intro ι _ _ r W hSep hRange hLarge
  classical
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 0 < ⌊T^a⌋₊ := by
    have hTwo : 2 ≤ ⌊T^a⌋₊ := Nat.le_floor hPower
    omega
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
    rw [Fintype.card_of_isEmpty,Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTPos.le _)
  | inr hNonempty =>
    let x₀ : ι := Classical.arbitrary _
    rcases hClassify T (W x₀) ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r
      hTClass rfl hY (hRange x₀).1 (hRange x₀).2 (hLarge x₀)
      with hBottomCase | ⟨hLower,hUpper,hScaleOne⟩
    · exact (hBottomT r W hBottomCase hSep hRange hLarge).trans
        (mul_le_mul_of_nonneg_right hCBLe (Real.rpow_nonneg hTPos.le _))
    · have hr : 2 ≤ r := by
        by_contra hnot
        have hPow : 2^r ≤ 2 := by
          simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : r ≤ 1)
        have hQUpper : 2^r*⌊T^a⌋₊ ≤ 2*⌊T^a⌋₊ :=
          Nat.mul_le_mul_right _ hPow
        have hCast : ((2^r*⌊T^a⌋₊ : ℕ) : ℝ) ≤ 2*(⌊T^a⌋₊ : ℝ) := by
          exact_mod_cast hQUpper
        have hLower' : (⌊T^a⌋₊ : ℝ)+1 ≤ ((2^r*⌊T^a⌋₊ : ℕ) : ℝ)/2 := by
          simpa only [Nat.cast_add,Nat.cast_one] using hLower
        linarith
      rcases lt_or_ge (typeILogarithmicScale T (2^r*⌊T^a⌋₊)) 2 with hScaleTwo | hScaleTwo
      · have hRangeR : ∀ x, T-T^dR ≤ W x ∧ W x ≤ 2*T+T^dR := by
          have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hdRLe
          intro x
          constructor <;> linarith [(hRange x).1,(hRange x).2]
        exact (hReflectedT W hTR rfl hY hr hLower hUpper rfl hScaleOne hScaleTwo
          hRangeR hLarge hSep).trans
          (mul_le_mul_of_nonneg_right hCRLe (Real.rpow_nonneg hTPos.le _))
      · have hRangeD : ∀ x, T-T^dD ≤ W x ∧ W x ≤ 2*T+T^dD := by
          have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hdDLe
          intro x
          constructor <;> linarith [(hRange x).1,(hRange x).2]
        exact (hDirectT r W hr hLower hUpper hScaleTwo hRangeD hLarge hSep).trans
          (mul_le_mul_of_nonneg_right hCDLe (Real.rpow_nonneg hTPos.le _))

theorem classicalGlobal_uniform_source_block_energy_bound
    (σ B a : ℝ) (hσ : 1/2 < σ) (hσOne : σ < 1)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (σ-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (σ-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, σ-eta ≤ s → s ≤ σ → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
                  (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                  (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                  (∀ x,
                    ((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ) ≤
                      ‖typeISourceSmoothBlock ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r s (W x)‖) →
                  (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨CB,hCB,δB,hδB,hBottom⟩ :=
    classicalBottom_uniform_shifted_line_source_energy_bound σ B a hB ha hGeneral ε hε
  obtain ⟨etaR,hEtaR,hEtaRGap,dR,hdR,hdRGap,_hdREps,CR,hCR,hReflected⟩ :=
    classicalReflected_uniform_shifted_line_source_energy_bound σ B hσ hσOne hB
      (fun τ hτ => hZeta τ hτ.1) ε hε
  obtain ⟨etaD,hEtaD,_hEtaDGap,dD,hdD,_hdDQuarter,_hdDEps,CD,hCD,hDirect⟩ :=
    classicalDirect_uniform_shifted_line_source_energy_bound σ B a hσ hB ha haHalf
      (fun τ hτ => hZeta τ hτ.1) ε hε
  let eta := min etaR (min etaD (δB/4))
  have hEta : 0 < eta := by dsimp [eta]; positivity
  have hEtaRLe : eta ≤ etaR := min_le_left _ _
  have hEtaDLe : eta ≤ etaD := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaBLe : eta ≤ δB/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hEtaGap : eta ≤ (σ-1/2)/2 := hEtaRLe.trans hEtaRGap
  let d := min dR (min dD (min (a*δB/8) (ε/100)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdRLe : d ≤ dR := min_le_left _ _
  have hdDLe : d ≤ dD := (min_le_right _ _).trans (min_le_left _ _)
  have hdRest : d ≤ min (a*δB/8) (ε/100) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdB : d ≤ a*δB/8 := hdRest.trans (min_le_left _ _)
  have hdEps : d ≤ ε/100 := hdRest.trans (min_le_right _ _)
  have hdGap : d ≤ (σ-1/2)/2000 := hdRLe.trans hdRGap
  let C := max CB (max CR CD)
  have hC : 1 ≤ C := hCB.trans (le_max_left _ _)
  have hCBLe : CB ≤ C := le_max_left _ _
  have hCRLe : CR ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCDLe : CD ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEps,C,hC,?_⟩
  intro s u hsLower hsUpper hu huD
  have hs : 1/2 < s := by linarith
  have hsOne : s < 1 := hsUpper.trans_lt hσOne
  have hdOne : d ≤ 1 := by linarith
  have hdSourceGap : d ≤ (s-1/2)/1000 := by linarith
  obtain ⟨TR,_hTR,hReflectedT⟩ :=
    hReflected s u (by linarith) hsUpper hu (huD.trans hdRLe)
  obtain ⟨TClass,_hTClass,hClassify⟩ :=
    eventually_large_global_source_classification s d u hs hsOne hd hdSourceGap huD
  filter_upwards [
    hBottom s u d (by linarith) hsOne.le (by linarith) (huD.trans hdB) hdOne,
    hDirect s u (by linarith) hu (huD.trans hdDLe),
    Filter.eventually_ge_atTop TR,Filter.eventually_ge_atTop TClass,
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)]
    with T hBottomT hDirectT hTR hTClass hPower hT
  intro ι _ _ r W hSep hRange hLarge
  classical
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 0 < ⌊T^a⌋₊ := by
    have hTwo : 2 ≤ ⌊T^a⌋₊ := Nat.le_floor hPower
    omega
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
    have hz : approximateAdditiveEnergyOf 1 W = 0 := by
      simp [approximateAdditiveEnergyOf,AdditiveQuadrupleOf]
    rw [hz,Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTPos.le _)
  | inr hNonempty =>
    let x₀ : ι := Classical.arbitrary _
    rcases hClassify T (W x₀) ⌊T^a⌋₊ ⌊sharpZetaCutoff T⌋₊ r
      hTClass rfl hY (hRange x₀).1 (hRange x₀).2 (hLarge x₀)
      with hBottomCase | ⟨hLower,hUpper,hScaleOne⟩
    · exact (hBottomT r W hBottomCase hSep hRange hLarge).trans
        (mul_le_mul_of_nonneg_right hCBLe (Real.rpow_nonneg hTPos.le _))
    · have hr : 2 ≤ r := by
        by_contra hnot
        have hPow : 2^r ≤ 2 := by
          simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : r ≤ 1)
        have hQUpper : 2^r*⌊T^a⌋₊ ≤ 2*⌊T^a⌋₊ :=
          Nat.mul_le_mul_right _ hPow
        have hCast : ((2^r*⌊T^a⌋₊ : ℕ) : ℝ) ≤ 2*(⌊T^a⌋₊ : ℝ) := by
          exact_mod_cast hQUpper
        have hLower' : (⌊T^a⌋₊ : ℝ)+1 ≤ ((2^r*⌊T^a⌋₊ : ℕ) : ℝ)/2 := by
          simpa only [Nat.cast_add,Nat.cast_one] using hLower
        linarith
      rcases lt_or_ge (typeILogarithmicScale T (2^r*⌊T^a⌋₊)) 2 with hScaleTwo | hScaleTwo
      · have hRangeR : ∀ x, T-T^dR ≤ W x ∧ W x ≤ 2*T+T^dR := by
          have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hdRLe
          intro x
          constructor <;> linarith [(hRange x).1,(hRange x).2]
        exact (hReflectedT W hTR rfl hY hr hLower hUpper rfl hScaleOne hScaleTwo
          hRangeR hLarge hSep).trans
          (mul_le_mul_of_nonneg_right hCRLe (Real.rpow_nonneg hTPos.le _))
      · have hRangeD : ∀ x, T-T^dD ≤ W x ∧ W x ≤ 2*T+T^dD := by
          have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hdDLe
          intro x
          constructor <;> linarith [(hRange x).1,(hRange x).2]
        exact (hDirectT r W hr hLower hUpper hScaleTwo hRangeD hLarge hSep).trans
          (mul_le_mul_of_nonneg_right hCDLe (Real.rpow_nonneg hTPos.le _))

end TaoTrudgianYang2025
