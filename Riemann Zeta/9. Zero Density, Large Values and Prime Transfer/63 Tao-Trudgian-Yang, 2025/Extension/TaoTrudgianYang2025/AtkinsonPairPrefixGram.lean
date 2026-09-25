import TaoTrudgianYang2025.AtkinsonGapPhysicalScale
import TaoTrudgianYang2025.AtkinsonMaximalGram
import GuthMaynard.SecondDerivative

/-! Actual finite Atkinson Gram prefixes with the general exponent-pair bound. -/

noncomputable section
open RiemannZeta.GuthMaynard
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem ExponentPair.atkinson_physical_gap_sum_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M t u : ℝ) (a b : ℕ), 0 < H → 1 ≤ M →
        H ≤ u → u ≤ 2*H → u < t → t ≤ 2*H →
        Real.pi*M/(2*H) < η → M ≤ (a : ℝ) → (b : ℝ) ≤ 2*M →
        ‖∑ n ∈ Finset.Icc a b,
          unitaryPhase (atkinsonSourcePhase t n-atkinsonSourcePhase u n)‖ ≤
          C*(((t-u)/Real.sqrt (H*M))^(k+ε)*M^(l+ε)+
            Real.sqrt (H*M)/(t-u)) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := hpair.atkinson_gap_sum_bound hε
  refine ⟨η,hη,12*C,by linarith,?_⟩
  intro H M t u a b hH hM hu hu2 htu ht2 hsmall ha hb
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hup : 0 < u := hH.trans_le hu
  have hgap : 0 < t-u := sub_pos.mpr htu
  have htU : t ≤ 2*u := by linarith
  have hq : Real.pi*M/(2*u) < η :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2*H)
      (by linarith : 2*H ≤ 2*u)).trans_lt hsmall
  have h := hbound M t u a b hM hup htu htU hq ha hb
  obtain ⟨hf,hi⟩ := atkinsonGap_frequency_physical_bounds hH hMp hu hu2 htu htU
  have hfp := atkinsonGapFrequency_pos hMp hup htu
  have hp : (atkinsonGapFrequency M t u/(2*Real.pi*M))^(k+ε)*M^(l+ε) ≤
      ((t-u)/Real.sqrt (H*M))^(k+ε)*M^(l+ε) :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) hf (by linarith [hpair.inTriangle.1]))
      (Real.rpow_nonneg hMp.le _)
  apply h.trans
  calc
    _ ≤ C*(((t-u)/Real.sqrt (H*M))^(k+ε)*M^(l+ε)+
        12*Real.sqrt (H*M)/(t-u)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hi) (by linarith)
    _ ≤ _ := by
      have hn : 0 ≤ C*(((t-u)/Real.sqrt (H*M))^(k+ε)*M^(l+ε)) := by positivity
      ring_nf at hn ⊢
      nlinarith

theorem atkinsonPrefixGram_succ_eq_sum (M j : ℕ) (t u : ℝ) :
    atkinsonPrefixGram M (j+1) u t =
      ∑ n ∈ Finset.Icc M (M+j),
        unitaryPhase (atkinsonSourcePhase t n-atkinsonSourcePhase u n) := by
  rw [sum_Icc_eq_shifted_range _ M (M+j) (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rfl

theorem ExponentPair.atkinson_prefixGramMax_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H t u : ℝ) (M : ℕ), 0 < H → 0 < M →
        H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H → t ≠ u →
        Real.pi*(M : ℝ)/(2*H) < η →
        atkinsonPrefixGramMax M M t u ≤
          C*((|t-u|/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε)+
            Real.sqrt (H*(M : ℝ))/|t-u|) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := hpair.atkinson_physical_gap_sum_bound hε
  have ordered : ∀ (H t u : ℝ) (M : ℕ), 0 < H → 0 < M →
      H ≤ u → u ≤ 2*H → u < t → t ≤ 2*H →
      Real.pi*(M : ℝ)/(2*H) < η →
      atkinsonPrefixGramMax M M u t ≤
        C*(((t-u)/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε)+
          Real.sqrt (H*(M : ℝ))/(t-u)) := by
    intro H t u M hH hM hu hu2 htu ht2 hsmall
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    unfold atkinsonPrefixGramMax
    apply Finset.sup'_le
    intro j hj
    have hjM : j ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    cases j with
    | zero =>
      simp only [atkinsonPrefixGram,Finset.range_zero,Finset.sum_empty,norm_zero]
      positivity
    | succ j =>
      rw [atkinsonPrefixGram_succ_eq_sum]
      exact hbound H M t u M (M+j) hH hM1 hu hu2 htu ht2 hsmall le_rfl
        (by push_cast; have hjr : (j : ℝ) ≤ M := by exact_mod_cast (show j ≤ M by omega)
            linarith)
  refine ⟨η,hη,C,hC,?_⟩
  intro H t u M hH hM ht ht2 hu hu2 hne hsmall
  rcases lt_or_gt_of_ne hne with htu | hut
  · rw [abs_of_neg (sub_neg.mpr htu),neg_sub]
    exact ordered H u t M hH hM ht ht2 htu hu2 hsmall
  · rw [abs_of_pos (sub_pos.mpr hut),← atkinsonPrefixGramMax_swap]
    exact ordered H t u M hH hM hu hu2 hut ht2 hsmall

end TaoTrudgianYang2025
