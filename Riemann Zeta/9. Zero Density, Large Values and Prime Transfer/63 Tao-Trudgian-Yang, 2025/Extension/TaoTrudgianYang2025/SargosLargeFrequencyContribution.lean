import TaoTrudgianYang2025.SargosReciprocalFrequency
import TaoTrudgianYang2025.SargosFrequencyScaleBounds

/-! Aggregate the actual exponent-pair consumer over every large ordered sextuple. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_large_frequency_contribution {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M a : ℕ) (F : ℝ → ℝ) (T N : ℝ),
        1 ≤ H → H ≤ M → 1 ≤ N → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N → 0 < T →
        IsApproximateModelPhaseFunction F σ P δ → (H:ℝ)^3/N^2 ≤ η →
        (∑ q ∈ sargosLargeFrequencySextuples H,
          ‖∑ m ∈ sargosSextupleInterior M q,
            fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N a 1) q m)‖) ≤
          C*((H:ℝ)^(4+ε)*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)+
            (N^5/(modelPhaseJetCoefficient σ 4*T))*(H:ℝ)^ε) := by
  obtain ⟨δ,hδ,P,hP,η,hη,E,hE,hbound⟩ :=
    sargos_large_frequency_exponentPair_bound hkl hσ hε
  obtain ⟨D,hD,hcard⟩ := sargosSquareDiagonal_card_bound ε hε
  obtain ⟨R,hR,hrec⟩ := sargos_reciprocal_frequency_bound ε hε
  refine ⟨δ,hδ,P,hP,η,hη,E*(D+R),one_le_mul_of_one_le_of_one_le hE (by linarith),?_⟩
  intro H M a F T N hH hHM hN ha hb hT hF hsmall
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hD4 := modelPhaseJetCoefficient_pos hσ 4
  have hke : 0 ≤ k+ε := by linarith [hkl.inTriangle.1]
  let A := (modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)
  let B := N^5/(modelPhaseJetCoefficient σ 4*T)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqbound : ∀ q ∈ sargosLargeFrequencySextuples H,
      ‖∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N a 1) q m)‖ ≤
        E*(A+B*(12/|(sargosQuarticDifference q:ℝ)|)) := by
    intro q hq
    have hp := sargosLargeFrequency_pos hH q hq
    have he := hbound H M a F T N q hH hHM hN ha hb hT hF hp.2 hsmall
    have hs := sargosTransformedFrequency_secondary_eq hσ hNp hT q hp.1
    have hm := sargosTransformedFrequency_main_le hσ hNp hT hke q
    calc
      _ ≤ E*((sargosScaledTransformedTime σ N (|(sargosQuarticDifference q:ℝ)|/12) T/N)^(k+ε)*
          N^(l+ε)+N/sargosScaledTransformedTime σ N (|(sargosQuarticDifference q:ℝ)|/12) T) := he
      _ ≤ E*(A+B*(12/|(sargosQuarticDifference q:ℝ)|)) := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hm (by positivity)) le_rfl) (by linarith)
  have hc : ((sargosLargeFrequencySextuples H).card:ℝ) ≤ D*(H:ℝ)^(4+ε) := by
    have hh : ((sargosLargeFrequencySextuples H).card:ℝ) ≤ ((sargosSquareDiagonal H).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    exact hh.trans (hcard H hH)
  calc
    _ ≤ ∑ q ∈ sargosLargeFrequencySextuples H, E*(A+B*(12/|(sargosQuarticDifference q:ℝ)|)) :=
      Finset.sum_le_sum hqbound
    _ = E*(((sargosLargeFrequencySextuples H).card:ℝ)*A+
        B*(∑ q ∈ sargosLargeFrequencySextuples H, 12/|(sargosQuarticDifference q:ℝ)|)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      rw [← Finset.mul_sum (s := sargosLargeFrequencySextuples H)
        (f := fun q => 12/|(sargosQuarticDifference q:ℝ)|) B]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ E*((D*(H:ℝ)^(4+ε))*A+B*(R*(H:ℝ)^ε)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hc hA)
          (mul_le_mul_of_nonneg_left (hrec H hH) hB)) (by linarith)
    _ ≤ E*((D+R)*((H:ℝ)^(4+ε)*A)+(D+R)*(B*(H:ℝ)^ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have hd : D ≤ D+R := by linarith
      have hr : R ≤ D+R := by linarith
      have h1 := mul_le_mul_of_nonneg_right hd
        (show 0 ≤ (H:ℝ)^(4+ε)*A by positivity)
      have h2 := mul_le_mul_of_nonneg_right hr
        (show 0 ≤ B*(H:ℝ)^ε by positivity)
      nlinarith only [h1,h2]
    _ = _ := by dsimp [A,B]; ring

end TaoTrudgianYang2025
