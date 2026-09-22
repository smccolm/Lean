import TaoTrudgianYang2025.BetaBProcessMajorant
import GuthMaynard.SecondDerivative

/-! Finite exponential sums at the physical source scales. The sign and
radians conversion is proved, and the three boundary terms are retained. -/

noncomputable section

open Expdb RiemannZeta.GuthMaynard
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem betaModelSample_phase_eq_conj (F : ℝ → ℝ) (T N A x : ℝ) :
    unitaryPhase (betaModelSample F T N A x) =
      starRingEnd ℂ (oscillatory F T N (A+x)) := by
  rw [unitaryPhase,oscillatory,Real.fourierChar_apply,← Complex.exp_conj]
  congr 1
  simp only [betaModelSample,map_mul,Complex.conj_ofReal,Complex.conj_I,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,map_ofNat]
  ring

theorem norm_modelPhaseCore_le
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (hL : (L : ℝ) ≤ N) (hscale : T ≤ N^2) :
    ‖∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n)‖ ≤
      betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
        (2*Real.pi*(σ+1))*(Real.sqrt T+N/Real.sqrt T) := by
  let c := 2*Real.pi*modelPhaseCurvatureLower σ
  let C := 2*Real.pi*(σ+1)
  have hc : 0 < c := mul_pos (by positivity) (modelPhaseCurvatureLower_pos hσ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := vanDerCorput_B_process (fun n => betaModelSample F T N A n) L
    (c*T/N^2) (C*T/N^2) (by positivity)
    (fun n hn => by simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      (betaModelSample_secondDifference_bounds hσ hT hN hδ hF hstart hend n hn).1)
    (fun n hn => by simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      (betaModelSample_secondDifference_bounds hσ hT hN hδ hF hstart hend n hn).2)
  have heq : (∑ n ∈ Finset.range (L+1), unitaryPhase (betaModelSample F T N A n)) =
      starRingEnd ℂ (∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n)) := by
    simp only [betaModelSample_phase_eq_conj,map_sum]
  rw [heq] at hb
  change ‖star (∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n))‖ ≤ _ at hb
  rw [norm_star] at hb
  exact hb.trans (betaBProcess_majorant hN hT hc hC hL hscale)

theorem norm_sum_Icc_le_interior_add_three
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (a L : ℕ) :
    ‖∑ n ∈ Finset.Icc a (a+L+3), z n‖ ≤
      ‖∑ n ∈ Finset.range (L+1), z (a+1+n)‖+3 := by
  have heq : (∑ n ∈ Finset.Icc a (a+L+3), z n) =
      ((∑ n ∈ Finset.range (L+1), z (a+1+n))+z a)+z (a+L+2)+z (a+L+3) := by
    rw [sum_Icc_eq_shifted_range z a (a+L+3) (by omega)]
    rw [show a+L+3-a+1 = ((L+1)+1)+1+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ']
    simp only [Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [heq]
  calc
    _ ≤ (‖∑ n ∈ Finset.range (L+1), z (a+1+n)‖+‖z a‖)+
        ‖z (a+L+2)‖+‖z (a+L+3)‖ :=
      by
        have h₁ := norm_add_le (∑ n ∈ Finset.range (L+1), z (a+1+n)) (z a)
        have h₂ := norm_add_le ((∑ n ∈ Finset.range (L+1), z (a+1+n))+z a)
          (z (a+L+2))
        have h₃ := norm_add_le (((∑ n ∈ Finset.range (L+1), z (a+1+n))+z a)+
          z (a+L+2)) (z (a+L+3))
        linarith
    _ ≤ _ := by linarith [hz a,hz (a+L+2),hz (a+L+3)]

end TaoTrudgianYang2025
