import GafniTao.Pintz2023NearOneGramBounds
import GafniTao.Pintz2023HalaszEnergy

/-!
# Pintz's exact powered-block Halasz consumer

This is the source-facing assembly of the powered coefficient, its `d_n`
energy, the infinite diagonal, and the two explicit off-diagonal terms.  The
two remaining assumptions are concrete scale inequalities for those terms;
neither is a cardinality estimate or a restatement of the conclusion.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023HalaszKernelConstant : ℝ :=
  Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ)))

theorem pintz2023HalaszKernelConstant_pos :
    0 < pintz2023HalaszKernelConstant := by
  exact pintz2023HalaszKernel_uniform_lower_pos

/-- Full exact powered-block form of Pintz (4.19), through off-diagonal
absorption. -/
theorem exists_pintz2023_intervalPower_halasz_cardinality
    (h : ℕ) (epsilonCoeff epsilonZeta : ℝ)
    (hepsilonCoeff : 0 < epsilonCoeff)
    (hepsilonZeta : 0 < epsilonZeta)
    (hepsilonZetaUpper : epsilonZeta ≤ 1) :
    ∃ Ce Cd Co : ℝ, 0 < Ce ∧ 0 < Cd ∧ 0 < Co ∧
      ∀ (X U N : ℕ) (baseI Iset : Finset ℕ) (W : Finset ℝ)
        (xi eta lambda A T G : ℝ) (etaAt gammaAt : ℝ → ℝ),
      let E := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilonCoeff)
      let D := pintz2023NearOneDiagonalMajorant Cd N xi eta
      let Omain := Co * (4 * eta)⁻¹ *
        (2 * T + 3) ^ pintz2023NearOneGramExponent xi eta epsilonZeta
      let Ores := Co * (4 * eta)⁻¹ *
        (3 * (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
          Real.exp (-G))
      baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N →
      Iset ⊆ Finset.Ioc N (2 * N) →
      -1 - 4 * eta - 2 / lambda + 2 * epsilonCoeff ≤ 0 →
      0 < eta →
      pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 4 →
      1 ≤ T → 1 ≤ G →
      0 ≤ A →
      (∀ t ∈ W, etaAt t ∈ Set.Icc 0 xi) →
      (∀ t ∈ W, |gammaAt t| ≤ T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → G ≤ |gammaAt u - gammaAt t|) →
      (∀ t ∈ W,
        A ≤ ‖∑ n ∈ Iset,
          pintz2023IntervalPowerCoeff X baseI h n *
            (n : ℂ) ^
              (-(((1 - etaAt t + 1 / lambda : ℝ) : ℂ) +
                I * ((gammaAt t : ℝ) : ℂ)))‖) →
      E * Omain ≤ A ^ 2 / 4 →
      E * Ores ≤ A ^ 2 / 4 →
      (W.card : ℝ) * A ^ 2 ≤ 2 * E * D := by
  obtain ⟨Ce, hCe, hEnergyBound⟩ :=
    exists_sum_norm_pintz2023IntervalPowerHalaszD_sq_le
      h epsilonCoeff hepsilonCoeff
  obtain ⟨Cd, hCd, hDiagonalBound⟩ :=
    exists_pintz2023NearOneDiagonalMajorant
  obtain ⟨Co, hCo, hOffDiagonalBound⟩ :=
    exists_pintz2023NearOneOffDiagonalMajorant
      hepsilonZeta hepsilonZetaUpper
  refine ⟨Ce, Cd, Co, hCe, hCd, hCo, ?_⟩
  intro X U N baseI Iset W xi eta lambda A T G etaAt gammaAt
  dsimp only
  intro hbaseI hU hN hIset hExponent heta hMax hT hG
    hA hetaAt hgammaAt hSeparated hLarge hAbsorbMain hAbsorbRes
  let E : ℝ := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
    (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilonCoeff)
  let D : ℝ := pintz2023NearOneDiagonalMajorant Cd N xi eta
  let Omain : ℝ := Co * (4 * eta)⁻¹ *
    (2 * T + 3) ^ pintz2023NearOneGramExponent xi eta epsilonZeta
  let Ores : ℝ := Co * (4 * eta)⁻¹ *
    (3 * (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
      Real.exp (-G))
  let O : ℝ := Omain + Ores
  have hPositive : ∀ n ∈ Iset, 0 < n := by
    intro n hn
    have hnIoc := hIset hn
    exact lt_trans hN (Finset.mem_Ioc.mp hnIoc).1
  have hEnergyRaw := hEnergyBound X U N baseI Iset Iset eta lambda
    hbaseI hU hN (by rfl) hPositive hIset hExponent
  have hEnergy :
      (∑ n ∈ Iset,
        ‖pintz2023IntervalPowerCoeff X baseI h n‖ ^ 2 *
          (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) ≤ E := by
    rw [sum_norm_pintz2023HalaszDSupported_sq Iset Iset
      (pintz2023IntervalPowerCoeff X baseI h) eta lambda hN
      (by rfl) hPositive] at hEnergyRaw
    simpa only [E, pintz2023HalaszKernelConstant] using hEnergyRaw
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
    have hBound := hOffDiagonalBound N xi eta (etaAt t) (etaAt u)
      (gammaAt t) (gammaAt u) T G hN heta (hetaAt t ht)
      (hetaAt u hu) hMax hT hG (hgammaAt t ht) (hgammaAt u hu)
      (hSeparated t ht u hu htu)
    simpa only [O, Omain, Ores, pintz2023NearOneOffDiagonalMajorant,
      mul_add] using hBound
  have hENonneg : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg Ce)
        (inv_nonneg.mpr pintz2023HalaszKernelConstant_pos.le))
      (Real.rpow_nonneg (by positivity) _)
  have hDNonneg : 0 ≤ D := by
    dsimp only [D, pintz2023NearOneDiagonalMajorant]
    positivity
  have hOMainNonneg : 0 ≤ Omain := by
    dsimp only [Omain]
    positivity
  have hOResNonneg : 0 ≤ Ores := by
    dsimp only [Ores]
    positivity
  have hONonneg : 0 ≤ O := by
    dsimp only [O]
    positivity
  have hAbsorb : E * O ≤ A ^ 2 / 2 := by
    dsimp only [O]
    rw [mul_add]
    nlinarith
  have hResult := pintz2023_halasz_cardinality_of_infinite_gram
    Iset W (pintz2023IntervalPowerCoeff X baseI h)
    eta lambda A E D O etaAt gammaAt hN hA
    hENonneg hDNonneg hONonneg hPositive hReal hLarge hEnergy
    hDiagonal hOffDiagonal hAbsorb
  simpa only [E, D] using hResult

#print axioms pintz2023HalaszKernelConstant_pos
#print axioms exists_pintz2023_intervalPower_halasz_cardinality

end

end GafniTao
