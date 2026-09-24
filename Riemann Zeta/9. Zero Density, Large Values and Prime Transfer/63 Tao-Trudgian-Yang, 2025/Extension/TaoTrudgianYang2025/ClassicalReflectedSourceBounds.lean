import TaoTrudgianYang2025.ClassicalReflectedLoss

/-!
# Uniform epsilon-loss bounds for the fixed-line interior source branch

The perturbation exponent and final constant precede all threshold-loss
choices, physical scales and indexed source families. Every explicit
reflection, Fourier, height, dyadic and separation loss is discharged.
Only the actual smooth interior source branch (1 < tau < 2) is claimed;
the other branches and global endpoint-two zero transfer remain separate.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_uniform_interior_source_cardinality_bound
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (2/((sigma-1/2)/2)),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ d : ℝ, 0 < d ∧ d ≤ (sigma-1/2)/1000 ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ u : ℝ, 0 ≤ u → u ≤ d →
            ∃ T₀ : ℝ, 8 ≤ T₀ ∧
              ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
                {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
                A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
                ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
                2*(2^r*Y) ≤ A →
                tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
                (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                  ‖typeISourceSmoothBlock Y A r sigma (W x)‖) →
                (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                (Fintype.card ι : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨Craw,hCraw,delta,hdelta,hfinite⟩ :=
    classicalReflected_interior_source_cardinality_transfer
      sigma B hsigma hsigmaUpper hB hLV (ε/2) (by linarith)
  let U : ℝ := 2/((sigma-1/2)/2)
  have hU : 0 < U := by dsimp [U]; positivity
  let d := min ((sigma-1/2)/1000)
    (min (delta/8) (min (delta/(8*U)) (ε/36)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdGap : d ≤ (sigma-1/2)/1000 := min_le_left _ _
  have hrest : d ≤ min (delta/8) (min (delta/(8*U)) (ε/36)) := min_le_right _ _
  have hdWindow : d ≤ delta/8 := hrest.trans (min_le_left _ _)
  have hrest' : d ≤ min (delta/(8*U)) (ε/36) := hrest.trans (min_le_right _ _)
  have hdNormalized : d ≤ delta/(8*U) := hrest'.trans (min_le_left _ _)
  have hdEpsilon : d ≤ ε/36 := hrest'.trans (min_le_right _ _)
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  obtain ⟨Kcard,Kenergy,hKcard,hKenergy,hLoss⟩ :=
    eventually_classicalReflected_losses_le_const_mul_rpow d (1+2*Real.pi)
      hd (by positivity)
  obtain ⟨Tloss,hLossAt⟩ := Filter.eventually_atTop.mp hLoss
  let Cfinal := max 1 (Kcard*Craw*2^B)
  have hCfinal : 1 ≤ Cfinal := le_max_left _ _
  have hCrawNonneg : 0 ≤ Craw := zero_le_one.trans hCraw
  refine ⟨d,hd,hdGap,Cfinal,hCfinal,?_⟩
  intro u hu huD
  have hSourceLoss : U*(u+3*d) ≤ delta/2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 8*U)).mp hdNormalized
    have huMul := mul_le_mul_of_nonneg_left huD hU.le
    nlinarith
  obtain ⟨Tsource,hTsource,hsource⟩ :=
    hfinite d u hd hdGap hu huD hdWindow hSourceLoss
  refine ⟨max Tsource Tloss,hTsource.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge hsep
  have hTEight : 8 ≤ T := hTsource.trans ((le_max_left _ _).trans hT)
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hEstimate := hsource W ((le_max_left _ _).trans hT) hA hY hr
    hLower hUpper hTau htauOne htauTwo hRange hLarge hsep
  let Q := 2^r*Y
  let M := mediumTypeIDualCutoff T d Q
  let D := T^d+2*Real.pi*T^d
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2^r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have hFour : 4 ≤ Q := hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : ℝ)^tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hM := classicalReflected_dualCutoff_le_sharpCutoff hTEight (by linarith)
    htauTwo.le hdHalf hQOne hScale
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDUpper : D ≤ (1+2*Real.pi)*T^d := by dsimp [D]; exact le_of_eq (by ring)
  have hLossBound := (hLossAt T ((le_max_right _ _).trans hT) M D hM hD hDUpper).1
  have hBase : (Fintype.card ι : ℝ) ≤
      classicalReflectedCardinalityLoss M D*(Craw*(2*T)^B*T^(ε/2)) := by
    convert hEstimate using 1
    dsimp [classicalReflectedCardinalityLoss,classicalReflectedColorCount,M,D,Q]
    ring
  calc
    (Fintype.card ι : ℝ) ≤ classicalReflectedCardinalityLoss M D*(Craw*(2*T)^B*T^(ε/2)) := hBase
    _ ≤ (Kcard*T^(2*d))*(Craw*(2*T)^B*T^(ε/2)) :=
      mul_le_mul_of_nonneg_right hLossBound (by positivity)
    _ = (Kcard*Craw*2^B)*T^(B+ε/2+2*d) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTPos.le]
      rw [Real.rpow_add hTPos, Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
        (Real.rpow_nonneg hTPos.le _) (zero_le_one.trans hCfinal)

theorem classicalReflected_uniform_interior_source_energy_bound
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (2/((sigma-1/2)/2)),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ d : ℝ, 0 < d ∧ d ≤ (sigma-1/2)/1000 ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ u : ℝ, 0 ≤ u → u ≤ d →
            ∃ T₀ : ℝ, 8 ≤ T₀ ∧
              ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
                {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
                A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
                ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
                2*(2^r*Y) ≤ A →
                tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
                (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
                (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                  ‖typeISourceSmoothBlock Y A r sigma (W x)‖) →
                (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
                (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨Craw,hCraw,delta,hdelta,hfinite⟩ :=
    classicalReflected_interior_source_energy_transfer
      sigma B hsigma hsigmaUpper hB hLV (ε/2) (by linarith)
  let U : ℝ := 2/((sigma-1/2)/2)
  have hU : 0 < U := by dsimp [U]; positivity
  let d := min ((sigma-1/2)/1000)
    (min (delta/8) (min (delta/(8*U)) (ε/36)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdGap : d ≤ (sigma-1/2)/1000 := min_le_left _ _
  have hrest : d ≤ min (delta/8) (min (delta/(8*U)) (ε/36)) := min_le_right _ _
  have hdWindow : d ≤ delta/8 := hrest.trans (min_le_left _ _)
  have hrest' : d ≤ min (delta/(8*U)) (ε/36) := hrest.trans (min_le_right _ _)
  have hdNormalized : d ≤ delta/(8*U) := hrest'.trans (min_le_left _ _)
  have hdEpsilon : d ≤ ε/36 := hrest'.trans (min_le_right _ _)
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  obtain ⟨Kcard,Kenergy,hKcard,hKenergy,hLoss⟩ :=
    eventually_classicalReflected_losses_le_const_mul_rpow d (1+2*Real.pi)
      hd (by positivity)
  obtain ⟨Tloss,hLossAt⟩ := Filter.eventually_atTop.mp hLoss
  let Cfinal := max 1 (Kenergy*Craw*2^B)
  have hCfinal : 1 ≤ Cfinal := le_max_left _ _
  have hCrawNonneg : 0 ≤ Craw := zero_le_one.trans hCraw
  refine ⟨d,hd,hdGap,Cfinal,hCfinal,?_⟩
  intro u hu huD
  have hSourceLoss : U*(u+3*d) ≤ delta/2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 8*U)).mp hdNormalized
    have huMul := mul_le_mul_of_nonneg_left huD hU.le
    nlinarith
  obtain ⟨Tsource,hTsource,hsource⟩ :=
    hfinite d u hd hdGap hu huD hdWindow hSourceLoss
  refine ⟨max Tsource Tloss,hTsource.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge hsep
  have hTEight : 8 ≤ T := hTsource.trans ((le_max_left _ _).trans hT)
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hEstimate := hsource W ((le_max_left _ _).trans hT) hA hY hr
    hLower hUpper hTau htauOne htauTwo hRange hLarge hsep
  let Q := 2^r*Y
  let M := mediumTypeIDualCutoff T d Q
  let D := T^d+2*Real.pi*T^d
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2^r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have hFour : 4 ≤ Q := hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : ℝ)^tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hM := classicalReflected_dualCutoff_le_sharpCutoff hTEight (by linarith)
    htauTwo.le hdHalf hQOne hScale
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDUpper : D ≤ (1+2*Real.pi)*T^d := by dsimp [D]; exact le_of_eq (by ring)
  have hLossBound := (hLossAt T ((le_max_right _ _).trans hT) M D hM hD hDUpper).2
  have hBase : (approximateAdditiveEnergyOf 1 W : ℝ) ≤
      classicalReflectedEnergyLoss M D*(Craw*(2*T)^B*T^(ε/2)) := by
    convert hEstimate using 1
    dsimp [classicalReflectedEnergyLoss,classicalReflectedColorCount,M,D,Q]
    ring
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤ classicalReflectedEnergyLoss M D*(Craw*(2*T)^B*T^(ε/2)) := hBase
    _ ≤ (Kenergy*T^(9*d))*(Craw*(2*T)^B*T^(ε/2)) :=
      mul_le_mul_of_nonneg_right hLossBound (by positivity)
    _ = (Kenergy*Craw*2^B)*T^(B+ε/2+9*d) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTPos.le]
      rw [Real.rpow_add hTPos, Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
        (Real.rpow_nonneg hTPos.le _) (zero_le_one.trans hCfinal)


end TaoTrudgianYang2025

