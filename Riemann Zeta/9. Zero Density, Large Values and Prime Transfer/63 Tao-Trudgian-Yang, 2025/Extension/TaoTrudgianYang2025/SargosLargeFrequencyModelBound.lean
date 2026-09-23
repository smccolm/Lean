import TaoTrudgianYang2025.SargosInnerModelEntry
import TaoTrudgianYang2025.ExponentPairAllHeights

/-! A genuine exponent-pair consumer for every actual large-frequency sextuple. -/

noncomputable section

open Set Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_large_frequency_error {H : ℕ} {N τ η : ℝ}
    (hN : 0 < N) (hτ : 0 < τ)
    (hlarge : (H:ℝ)^3 ≤ τ) (hsmall : (H:ℝ)^3/N^2 ≤ η) :
    (H:ℝ)^6/(τ*N^2) ≤ η := by
  apply (div_le_iff₀ (mul_pos hτ (pow_pos hN 2))).mpr
  have hs := (div_le_iff₀ (pow_pos hN 2)).mp hsmall
  rw [show (H:ℝ)^6 = (H:ℝ)^3*(H:ℝ)^3 by ring]
  calc
    _ ≤ τ*((H:ℝ)^3) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ ≤ τ*(η*N^2) := mul_le_mul_of_nonneg_left hs hτ.le
    _ = _ := by ring

theorem sargos_large_frequency_exponentPair_bound {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M a : ℕ) (F : ℝ → ℝ) (T N : ℝ)
        (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
        1 ≤ H → H ≤ M → 1 ≤ N → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N → 0 < T →
        IsApproximateModelPhaseFunction F σ P δ →
        let τ : ℝ := |(sargosQuarticDifference q:ℝ)|/12
        (H:ℝ)^3 ≤ τ → (H:ℝ)^3/N^2 ≤ η →
        ‖∑ m ∈ sargosSextupleInterior M q,
          fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N a 1) q m)‖ ≤
          C*((sargosScaledTransformedTime σ N τ T/N)^(k+ε)*N^(l+ε)+
            N/sargosScaledTransformedTime σ N τ T) := by
  obtain ⟨d,hd,P,hP,C,hC,hpair⟩ :=
    hkl.allPositiveHeight_bound (σ := σ+4) (by linarith) hε
  obtain ⟨B,hB,hmodel⟩ := sargos_scaled_oriented_sextuple_model σ hσ P
  let D := modelPhaseJetCoefficient σ 4
  have hD : 0 < D := modelPhaseJetCoefficient_pos hσ 4
  let δ := min 1 (d*D/2)
  let η := d*D/(2*B)
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨δ,hδ,P+7,by omega,η,hη,C,hC,?_⟩
  intro H M a F T N q hH hHM hN ha hb hT hF τ hlarge hsmall
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hτ : 0 < τ := (pow_pos hH0 3).trans_le hlarge
  have hq : sargosQuarticDifference q ≠ 0 := by
    intro he
    have hz : τ = 0 := by dsimp [τ]; rw [he]; norm_num
    linarith
  have ht := sargosScaledTransformedTime_pos hσ hN0 hτ hT
  have hm := hmodel H M F δ N a T q (hH.trans hHM) (min_le_left _ _)
    hN0 ha hb hT hq hF
  dsimp only at hm
  have he : (δ+B*(H:ℝ)^6/(τ*N^2))/D ≤ d := by
    have hs := sargos_large_frequency_error hN0 hτ hlarge hsmall
    have hscaled : B*(H:ℝ)^6/(τ*N^2) ≤ B*η := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hs hB0.le
    have hηeq : B*η = d*D/2 := by
      dsimp [η]
      field_simp
    apply (div_le_iff₀ hD).mpr
    have hδle : δ ≤ d*D/2 := min_le_right _ _
    linarith
  have happrox := approximateModelPhase_mono hm.1 le_rfl he
  rw [hm.2]
  by_cases hne : (sargosSextupleInterior M q).Nonempty
  · rw [sargos_inner_sum_eq_exponentialSumAt _ _ _ a M q hne]
    have hg := sargosInnerEndpoints_dyadic a M q hne ha hb
    exact hpair _ N _ _ _ ht hN hg.1 hg.2 happrox
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025
