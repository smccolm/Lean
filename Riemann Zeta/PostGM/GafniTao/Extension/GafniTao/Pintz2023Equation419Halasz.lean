import GafniTao.Pintz2023Equation417
import GafniTao.Pintz2023Equation419Absorption
import GafniTao.Pintz2023HalaszConsumer
import GafniTao.Pintz2023NearOneGramBounds
import GafniTao.Pintz2023SmallMIntervalPower

/-!
# Pintz (2023), equation (4.19): source Halasz consumer

This file assembles the exact surviving small-`m` coefficient, its weighted
energy, the diagonal Gram term, the completed two-range off-diagonal Gram
estimate, and the detector-threshold absorption.  The conclusion is the
cardinality estimate used after equation (4.19); no absorption inequality is
left as a hypothesis.
-/

open Complex Finset Filter
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal equation-(4.19) Halasz estimate for a fixed selected power.
All analytic constants are uniform in the physical height, the selected
dyadic block, and the zero family. -/
theorem exists_eventually_pintz2023_equation419_halasz_native
    {eta target : ℝ} {k ell h : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hh : 0 < h) :
    ∃ N₀ : ℕ, ∃ Ce Cd Cg : ℝ,
      0 < Ce ∧ 0 < Cd ∧ 0 < Cg ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ (X U N : ℕ) (R : ℝ) (baseI : Finset ℕ)
          (Z : Finset ℝ) (etaAt : ℝ → ℝ),
        let epsilonCoeff := data.epsilon / (100 * (k : ℝ))
        let A :=
          ((1 / (32 * Real.exp 2 *
                Real.log (pintz2023SourceLambda T k)) /
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
        let E := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
          (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff)
        let D := pintz2023NearOneDiagonalMajorant Cd N eta eta
        baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N → N₀ ≤ N →
        1 ≤ T →
        T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
        (N : ℝ) ≤ T ^ (3 : ℝ) →
        IsSeparated (3 * pintz2023SourceLambda T k) Z →
        (∀ u ∈ Z, etaAt u ∈ Set.Icc 0 eta) →
        (∀ u ∈ Z, ∀ v ∈ Z, |v - u| ≤ T) →
        (∀ u ∈ Z,
          A ≤ ‖dirichletPoly N
            (pintz2023SmallMPoweredLineCoeff X R baseI h
              (1 - etaAt u + 1 / pintz2023SourceLambda T k)) u‖) →
        (Z.card : ℝ) * A ^ 2 ≤ 2 * E * D := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  let epsilonCoeff : ℝ := data.epsilon / (100 * (k : ℝ))
  have hepsilonCoeff : 0 < epsilonCoeff := by
    dsimp only [epsilonCoeff]
    exact div_pos data.epsilon_pos (mul_pos (by norm_num) hkReal)
  obtain ⟨Ce, hCe, hEnergyBound⟩ :=
    exists_sum_norm_pintz2023SmallMIntervalPowerHalaszD_sq_le
      h epsilonCoeff hepsilonCoeff
  obtain ⟨Cd, hCd, hDiagonalBound⟩ :=
    exists_pintz2023NearOneDiagonalMajorant
  obtain ⟨N₀, Cg, hCg, hGram⟩ :=
    exists_pintz2023_equation419_offDiagonal_gram_native hcell data
  have hAbsorb := eventually_pintz2023_equation419_absorption
    hcell data hh hCg (Ce := Ce)
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  refine ⟨N₀, Ce, Cd, Cg, hCe, hCd, hCg, ?_⟩
  filter_upwards [hAbsorb,
    hLambda.eventually (eventually_ge_atTop 1)] with T hAbsorbT hLambdaOne
  intro X U N R baseI Z etaAt
  dsimp only
  intro hbaseI hU hN hN₀ hT hCritical hNUpper hSeparated hetaAt
    hDifference hDetected
  let A : ℝ :=
    ((1 / (32 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k)) /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
  let E : ℝ := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
    (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
      2 * epsilonCoeff)
  let D : ℝ := pintz2023NearOneDiagonalMajorant Cd N eta eta
  let O : ℝ := (N : ℝ) ^ (4 * eta) *
    (4 * (N : ℝ) ^ (-2 * data.epsilon) +
      Cg * (4 * eta)⁻¹ *
        ((4 ^ pintz2023NearOneGramExponent eta eta data.epsilon + 3) *
          T ^ (-data.epsilon / (k : ℝ))))
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLambdaPos : 0 < pintz2023SourceLambda T k := by
    exact zero_lt_one.trans_le hLambdaOne
  have hExponent :
      -1 - 4 * eta - 2 / pintz2023SourceLambda T k +
          2 * epsilonCoeff ≤ 0 := by
    have hellReal : (0 : ℝ) < ell := by
      exact_mod_cast (lt_of_lt_of_le (by omega) hcell.2.1)
    have hepsilonEta : data.epsilon ≤ eta := by
      have hHundredEll : (1 : ℝ) ≤ 100 * ell := by
        have hellOne : (1 : ℝ) ≤ ell := by
          exact_mod_cast (le_trans (by omega : 1 ≤ 3) hcell.2.1)
        nlinarith
      calc
        data.epsilon ≤ data.epsilon * (100 * (ell : ℝ)) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hHundredEll data.epsilon_pos.le
        _ ≤ eta := (le_div_iff₀ (mul_pos (by norm_num) hellReal)).mp
          data.equation420_small
    have hecEta : epsilonCoeff ≤ eta := by
      dsimp only [epsilonCoeff]
      have hDenOne : (1 : ℝ) ≤ 100 * k := by
        have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        nlinarith
      exact (div_le_iff₀ (mul_pos (by norm_num) hkReal)).2
        (by nlinarith [hepsilonEta, data.epsilon_pos])
    have hLambdaTerm : 0 ≤ 2 / pintz2023SourceLambda T k := by positivity
    nlinarith
  have hMax : pintz2023NearOneGramMaxDistance eta eta ≤ 1 / 4 := by
    unfold pintz2023NearOneGramMaxDistance
    nlinarith [data.eta_le_one_twentyFour]
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hlogLambda : 0 ≤ Real.log (pintz2023SourceLambda T k) :=
      Real.log_nonneg hLambdaOne
    have hbase : 0 ≤
        (1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 := by
      positivity
    exact div_nonneg (pow_nonneg hbase h) (Nat.cast_nonneg h)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg Ce)
        (inv_nonneg.mpr pintz2023HalaszKernelConstant_pos.le))
      (Real.rpow_nonneg hNReal.le _)
  have hD : 0 ≤ D := by
    dsimp only [D, pintz2023NearOneDiagonalMajorant]
    positivity
  have hO : 0 ≤ O := by
    dsimp only [O]
    positivity
  have hPositive : ∀ n ∈ dyadicInterval N, 0 < n := by
    intro n hn
    exact lt_trans hN (Finset.mem_Ioc.mp hn).1
  have hEnergyRaw := hEnergyBound X U N R baseI
    (dyadicInterval N) (dyadicInterval N) eta
    (pintz2023SourceLambda T k) hbaseI hU hN (by rfl)
    hPositive (by rfl) hExponent
  have hEnergy :
      (∑ n ∈ dyadicInterval N,
        ‖pintz2023SmallMIntervalPowerCoeff X R baseI h n‖ ^ 2 *
          (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta -
            2 / pintz2023SourceLambda T k)) ≤ E := by
    rw [sum_norm_pintz2023HalaszDSupported_sq
      (dyadicInterval N) (dyadicInterval N)
      (pintz2023SmallMIntervalPowerCoeff X R baseI h) eta
      (pintz2023SourceLambda T k) hN (by rfl) hPositive] at hEnergyRaw
    simpa only [E, pintz2023HalaszKernelConstant] using hEnergyRaw
  have hReal : ∀ t ∈ Z, ∀ u ∈ Z,
      0 ≤ 1 - etaAt t - etaAt u - 4 * eta := by
    intro t ht u hu
    nlinarith [data.eta_le_one_twentyFour,
      (hetaAt t ht).2, (hetaAt u hu).2]
  have hLarge : ∀ u ∈ Z,
      A ≤ ‖∑ n ∈ dyadicInterval N,
        pintz2023SmallMIntervalPowerCoeff X R baseI h n *
          (n : ℂ) ^
            (-(((1 - etaAt u + 1 / pintz2023SourceLambda T k : ℝ) : ℂ) +
              I * ((u : ℝ) : ℂ)))‖ := by
    intro u hu
    rw [← dirichletPoly_pintz2023SmallMPoweredLineCoeff_eq_equation417]
    exact hDetected u hu
  have hDiagonal : ∀ t ∈ Z,
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((t - t : ℝ) : ℂ)))‖ ≤ D := by
    intro t ht
    simpa only [D] using hDiagonalBound N eta eta (etaAt t) t
      hN heta (hetaAt t ht) hMax
  have hOffDiagonal : ∀ t ∈ Z, ∀ u ∈ Z, t ≠ u →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((u - t : ℝ) : ℂ)))‖ ≤ O := by
    intro t ht u hu htu
    have hSep : 3 * pintz2023SourceLambda T k ≤ |u - t| :=
      by simpa [Real.dist_eq, abs_sub_comm] using hSeparated t ht u hu htu
    have hSepOne : 1 ≤ |u - t| := by
      nlinarith
    have hRaw := hGram N (etaAt t) (etaAt u) t u T hN₀
      (hetaAt t ht) (hetaAt u hu) hSepOne (hDifference t ht u hu) hT
      hCritical hNUpper hSep
    have hScaled := mul_le_mul_of_nonneg_left hRaw
      (Real.rpow_nonneg hNReal.le (4 * eta))
    have hCancel :
        (N : ℝ) ^ (4 * eta) *
            ((N : ℝ) ^ (-4 * eta) *
              ‖pintz2023SmoothedZetaSum N
                (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
                  I * (((u - t : ℝ) : ℂ)))‖) =
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
              I * (((u - t : ℝ) : ℂ)))‖ := by
      rw [← mul_assoc, ← Real.rpow_add hNReal]
      norm_num
    simpa only [O, hCancel] using hScaled
  have hAbsorbEO : E * O ≤ A ^ 2 / 2 := by
    simpa only [E, O, A] using hAbsorbT N hT hN hCritical hNUpper
  exact pintz2023_halasz_cardinality_of_infinite_gram
    (dyadicInterval N) Z
    (pintz2023SmallMIntervalPowerCoeff X R baseI h)
    eta (pintz2023SourceLambda T k) A E D O etaAt id hN hA hE hD hO
    hPositive hReal hLarge hEnergy hDiagonal hOffDiagonal hAbsorbEO

#print axioms exists_eventually_pintz2023_equation419_halasz_native

end

end GafniTao
