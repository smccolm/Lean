import GafniTao.Pintz2023SplitGram
import GafniTao.Pintz2023SmallMIntervalPower

/-!
# Pintz (2023), equation (4.19) with the source two-range Gram estimate

This is the Halasz--Montgomery consumer for the actual small-`m` powered
coefficient.  Unlike the earlier near-one consumer, its off-diagonal input
is proved internally from the `B_h` versus `|t|^(1.9/r)` split.  The two
energy absorptions are still stated separately, as in equations
(4.20)--(4.23), so their exponent calculations can be audited.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem exists_pintz2023_split_intervalPower_halasz_cardinality
    (h r : ℕ) (eta epsilonCoeff epsilonZeta : ℝ)
    (hr : 3 ≤ r) (heta : 0 < eta)
    (hepsilonCoeff : 0 < epsilonCoeff)
    (hepsilonZeta : 0 < epsilonZeta)
    (hepsilonZetaUpper : 3 * epsilonZeta ≤ 1)
    (hTarget : 2 * epsilonZeta ≤ 4 * eta) :
    ∃ Ce Cd Co : ℝ, ∃ N₀ : ℕ,
      0 < Ce ∧ 0 < Cd ∧ 0 < Co ∧
      ∀ (X U N : ℕ) (R : ℝ) (baseI Iset : Finset ℕ)
        (W : Finset ℝ) (xi lambda A T G : ℝ)
        (etaAt gammaAt : ℝ → ℝ),
      let E := Ce ^ 2 *
        (Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))))⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilonCoeff)
      let D := pintz2023NearOneDiagonalMajorant Cd N xi eta
      let Osmall := 4 * (N : ℝ) ^ (4 * eta - 2 * epsilonZeta)
      let Olarge := pintz2023NearOneOffDiagonalMajorant
        Co N xi eta epsilonZeta T G
      N₀ ≤ N →
      baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N →
      Iset ⊆ Finset.Ioc N (2 * N) →
      -1 - 4 * eta - 2 / lambda + 2 * epsilonCoeff ≤ 0 →
      2 * xi + 6 * epsilonZeta ≤ pintz2023HBAlpha r →
      6 * (r : ℝ) * epsilonZeta <
        1 - ((r : ℝ) - 1) * (2 * xi) →
      pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 4 →
      1 ≤ T → 1 ≤ G → 0 ≤ A →
      (∀ t ∈ W, etaAt t ∈ Set.Icc 0 xi) →
      (∀ t ∈ W, |gammaAt t| ≤ T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u →
        G ≤ |gammaAt u - gammaAt t|) →
      pintz2023CriticalScale r (2 * xi) epsilonZeta (2 * T + 3) ≤
        (N : ℝ) →
      (∀ t ∈ W,
        A ≤ ‖∑ n ∈ Iset,
          pintz2023SmallMIntervalPowerCoeff X R baseI h n *
            (n : ℂ) ^
              (-(((1 - etaAt t + 1 / lambda : ℝ) : ℂ) +
                I * ((gammaAt t : ℝ) : ℂ)))‖) →
      E * Osmall ≤ A ^ 2 / 4 →
      E * Olarge ≤ A ^ 2 / 4 →
      (W.card : ℝ) * A ^ 2 ≤ 2 * E * D := by
  obtain ⟨Ce, hCe, hEnergyBound⟩ :=
    exists_sum_norm_pintz2023SmallMIntervalPowerHalaszD_sq_le
      h epsilonCoeff hepsilonCoeff
  obtain ⟨Cd, hCd, hDiagonalBound⟩ :=
    exists_pintz2023NearOneDiagonalMajorant
  obtain ⟨N₀, Co, hCo, hOffDiagonalBound⟩ :=
    exists_pintz2023_split_offDiagonal_gram_native
      r eta epsilonZeta hr heta hepsilonZeta hepsilonZetaUpper hTarget
  refine ⟨Ce, Cd, Co, N₀, hCe, hCd, hCo, ?_⟩
  intro X U N R baseI Iset W xi lambda A T G etaAt gammaAt
  dsimp only
  intro hN₀ hbaseI hU hN hIset hExponent hAlpha hDen hMax
    hT hG hA hetaAt hgammaAt hSeparated hCritical hLarge
    hAbsorbSmall hAbsorbLarge
  let E : ℝ := Ce ^ 2 *
    (Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))))⁻¹ *
    (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilonCoeff)
  let D : ℝ := pintz2023NearOneDiagonalMajorant Cd N xi eta
  let Osmall : ℝ := 4 * (N : ℝ) ^ (4 * eta - 2 * epsilonZeta)
  let Olarge : ℝ := pintz2023NearOneOffDiagonalMajorant
    Co N xi eta epsilonZeta T G
  let O : ℝ := Osmall + Olarge
  have hPositive : ∀ n ∈ Iset, 0 < n := by
    intro n hn
    exact lt_trans hN (Finset.mem_Ioc.mp (hIset hn)).1
  have hEnergyRaw := hEnergyBound X U N R baseI Iset Iset eta lambda
    hbaseI hU hN (by rfl) hPositive hIset hExponent
  have hEnergy :
      (∑ n ∈ Iset,
        ‖pintz2023SmallMIntervalPowerCoeff X R baseI h n‖ ^ 2 *
          (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) ≤ E := by
    rw [sum_norm_pintz2023HalaszDSupported_sq Iset Iset
      (pintz2023SmallMIntervalPowerCoeff X R baseI h)
      eta lambda hN (by rfl) hPositive] at hEnergyRaw
    simpa only [E] using hEnergyRaw
  have hReal : ∀ t ∈ W, ∀ u ∈ W,
      0 ≤ 1 - etaAt t - etaAt u - 4 * eta := by
    intro t ht u hu
    have htUpper := (hetaAt t ht).2
    have huUpper := (hetaAt u hu).2
    unfold pintz2023NearOneGramMaxDistance at hMax
    linarith
  have hDiagonal : ∀ t ∈ W,
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖ ≤ D := by
    intro t ht
    simpa only [D] using hDiagonalBound N xi eta (etaAt t) (gammaAt t)
      hN heta (hetaAt t ht) hMax
  have hOffDiagonal : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖ ≤ O := by
    intro t ht u hu htu
    have hBound := hOffDiagonalBound N xi (etaAt t) (etaAt u)
      (gammaAt t) (gammaAt u) T G hN₀ (hetaAt t ht) (hetaAt u hu)
      hAlpha hDen hMax hT hG (hgammaAt t ht) (hgammaAt u hu)
      (hSeparated t ht u hu htu) hCritical
    simpa only [O, Osmall, Olarge] using hBound
  have hENonneg : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg Ce)
        (inv_nonneg.mpr pintz2023HalaszKernel_uniform_lower_pos.le))
      (Real.rpow_nonneg (by positivity) _)
  have hDNonneg : 0 ≤ D := by
    dsimp only [D, pintz2023NearOneDiagonalMajorant]
    positivity
  have hOSmallNonneg : 0 ≤ Osmall := by
    dsimp only [Osmall]
    positivity
  have hOLargeNonneg : 0 ≤ Olarge := by
    dsimp only [Olarge, pintz2023NearOneOffDiagonalMajorant]
    positivity
  have hONonneg : 0 ≤ O := by
    dsimp only [O]
    positivity
  have hAbsorb : E * O ≤ A ^ 2 / 2 := by
    dsimp only [O]
    rw [mul_add]
    nlinarith
  have hResult := pintz2023_halasz_cardinality_of_infinite_gram
    Iset W (pintz2023SmallMIntervalPowerCoeff X R baseI h)
    eta lambda A E D O etaAt gammaAt hN hA
    hENonneg hDNonneg hONonneg hPositive hReal hLarge hEnergy
    hDiagonal hOffDiagonal hAbsorb
  simpa only [E, D] using hResult

#print axioms exists_pintz2023_split_intervalPower_halasz_cardinality

end

end GafniTao
