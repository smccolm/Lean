import TaoTrudgianYang2025.ClassicalDirectSourceLoss

/-!
# Uniform direct interior bounds with every finite loss absorbed

The common line window, displacement exponent and final constant precede
the source line and threshold-loss parameter. These are actual source
bounds at physical logarithmic scale at least two, not zero-density or
full zero-energy assembly claims.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirect_uniform_shifted_line_source_cardinality_bound
    (sigma B a : ℝ) (hsigma : 1/2 < sigma)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ 1/4 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                let A := ⌊sharpZetaCutoff T⌋₊
                ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
                  let Q := 2^r*Y
                  2 ≤ r → ((Y+1 : ℕ) : ℝ) ≤ (Q : ℝ)/2 → 2*Q ≤ A →
                  2 ≤ typeILogarithmicScale T Q →
                  (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                  (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                    ‖typeISourceSmoothBlock Y A r s (W x)‖) →
                  (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                  (Fintype.card ι : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨Craw,hCraw,delta,hdelta,hSource⟩ :=
    classicalDirect_shifted_line_source_cardinality_transfer
      sigma B a hB ha haHalf hLV (ε/2) (by linarith)
  let eta := min ((sigma-1/2)/2) (delta/4)
  have hEta : 0 < eta := by dsimp [eta]; positivity
  have hEtaGap : eta ≤ (sigma-1/2)/2 := min_le_left _ _
  have hEtaWindow : eta ≤ delta/4 := min_le_right _ _
  let d := min (1/4) (min (a*delta/4) (ε/100))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdQuarter : d ≤ 1/4 := min_le_left _ _
  have hdRest : d ≤ min (a*delta/4) (ε/100) := min_le_right _ _
  have hdLoss : d ≤ a*delta/4 := hdRest.trans (min_le_left _ _)
  have hdEpsilon : d ≤ ε/100 := hdRest.trans (min_le_right _ _)
  obtain ⟨Kcard,Kenergy,hKcard,hKenergy,hLoss⟩ :=
    eventually_classicalDirect_twoColor_losses_le_const_mul_rpow d (2*Real.pi)
      hd (by positivity)
  let Cfinal := max 1 (Kcard*Craw*2^B)
  have hCfinal : 1 ≤ Cfinal := le_max_left _ _
  have hCrawNonneg : 0 ≤ Craw := zero_le_one.trans hCraw
  refine ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,Cfinal,hCfinal,?_⟩
  intro s u hsLower hu huD
  have hs : 0 ≤ s := by linarith
  have hLine : sigma-delta/2 ≤ s := by linarith
  have hdOne : d < 1 := by linarith
  have huOne : u ≤ 1 := by linarith
  have huLoss : u ≤ a*delta/4 := huD.trans hdLoss
  filter_upwards [hSource s d u hs hLine hd hdOne huOne huLoss,
    hLoss,Filter.eventually_ge_atTop (8 : ℝ)] with T hSourceT hLossT hT
  dsimp only
  intro ι _ _ r W hr hLower hUpper hScale hRange hLarge hSep
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hEstimate := hSourceT r W hr hLower hUpper hScale hRange hLarge hSep
  let D := 2*Real.pi*T^d
  let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1))) : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hLossBound := (hLossT D hD le_rfl).1
  have hBase : (Fintype.card ι : ℝ) ≤
      (4*K)*(Craw*(2*T)^B*T^(ε/2)) := by
    convert hEstimate using 1
    dsimp [D,K]
    ring
  calc
    (Fintype.card ι : ℝ) ≤ (4*K)*(Craw*(2*T)^B*T^(ε/2)) := hBase
    _ ≤ (Kcard*T^(2*d))*(Craw*(2*T)^B*T^(ε/2)) :=
      mul_le_mul_of_nonneg_right hLossBound (by positivity)
    _ = (Kcard*Craw*2^B)*T^(B+ε/2+2*d) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTPos.le]
      rw [Real.rpow_add hTPos,Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
        (Real.rpow_nonneg hTPos.le _) (zero_le_one.trans hCfinal)

theorem classicalDirect_uniform_shifted_line_source_energy_bound
    (sigma B a : ℝ) (hsigma : 1/2 < sigma)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ 1/4 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                let A := ⌊sharpZetaCutoff T⌋₊
                ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
                  let Q := 2^r*Y
                  2 ≤ r → ((Y+1 : ℕ) : ℝ) ≤ (Q : ℝ)/2 → 2*Q ≤ A →
                  2 ≤ typeILogarithmicScale T Q →
                  (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                  (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                    ‖typeISourceSmoothBlock Y A r s (W x)‖) →
                  (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                  (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨Craw,hCraw,delta,hdelta,hSource⟩ :=
    classicalDirect_shifted_line_source_energy_transfer
      sigma B a hB ha haHalf hLV (ε/2) (by linarith)
  let eta := min ((sigma-1/2)/2) (delta/4)
  have hEta : 0 < eta := by dsimp [eta]; positivity
  have hEtaGap : eta ≤ (sigma-1/2)/2 := min_le_left _ _
  have hEtaWindow : eta ≤ delta/4 := min_le_right _ _
  let d := min (1/4) (min (a*delta/4) (ε/100))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdQuarter : d ≤ 1/4 := min_le_left _ _
  have hdRest : d ≤ min (a*delta/4) (ε/100) := min_le_right _ _
  have hdLoss : d ≤ a*delta/4 := hdRest.trans (min_le_left _ _)
  have hdEpsilon : d ≤ ε/100 := hdRest.trans (min_le_right _ _)
  obtain ⟨Kcard,Kenergy,hKcard,hKenergy,hLoss⟩ :=
    eventually_classicalDirect_twoColor_losses_le_const_mul_rpow d (2*Real.pi)
      hd (by positivity)
  let Cfinal := max 1 (Kenergy*Craw*2^B)
  have hCfinal : 1 ≤ Cfinal := le_max_left _ _
  have hCrawNonneg : 0 ≤ Craw := zero_le_one.trans hCraw
  refine ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,Cfinal,hCfinal,?_⟩
  intro s u hsLower hu huD
  have hs : 0 ≤ s := by linarith
  have hLine : sigma-delta/2 ≤ s := by linarith
  have hdOne : d < 1 := by linarith
  have huOne : u ≤ 1 := by linarith
  have huLoss : u ≤ a*delta/4 := huD.trans hdLoss
  filter_upwards [hSource s d u hs hLine hd hdOne huOne huLoss,
    hLoss,Filter.eventually_ge_atTop (8 : ℝ)] with T hSourceT hLossT hT
  dsimp only
  intro ι _ _ r W hr hLower hUpper hScale hRange hLarge hSep
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hEstimate := hSourceT r W hr hLower hUpper hScale hRange hLarge hSep
  let D := 2*Real.pi*T^d
  let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1))) : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hLossBound := (hLossT D hD le_rfl).2
  have hBase : (approximateAdditiveEnergyOf 1 W : ℝ) ≤
      ((4*Nat.ceil (1+4*D)+6)*9*K^4*2304)*(Craw*(2*T)^B*T^(ε/2)) := by
    convert hEstimate using 1
    dsimp [D,K]
    ring
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤ ((4*Nat.ceil (1+4*D)+6)*9*K^4*2304)*(Craw*(2*T)^B*T^(ε/2)) := hBase
    _ ≤ (Kenergy*T^(9*d))*(Craw*(2*T)^B*T^(ε/2)) :=
      mul_le_mul_of_nonneg_right hLossBound (by positivity)
    _ = (Kenergy*Craw*2^B)*T^(B+ε/2+9*d) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTPos.le]
      rw [Real.rpow_add hTPos,Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
        (Real.rpow_nonneg hTPos.le _) (zero_le_one.trans hCfinal)

end TaoTrudgianYang2025
