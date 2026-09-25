import TaoTrudgianYang2025.AtkinsonPairPrefixGram
import TaoTrudgianYang2025.AtkinsonSeparatedReciprocal

/-! Summation of actual Atkinson prefix Gram rows with general exponent pairs. -/

noncomputable section
open RiemannZeta.GuthMaynard
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem ExponentPair.atkinson_pair_gram_row {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H G L t : ℝ) (M : ℕ) (W : Finset ℝ),
        0 < H → 0 < G → 0 < M → IsSeparated G W → t ∈ W →
        (∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) →
        (∀ u ∈ W, |u-t| ≤ L) → Real.pi*(M : ℝ)/(2*H) < η →
        (∑ u ∈ W, atkinsonPrefixGramMax M M t u) ≤
          (M : ℝ)+C*(W.card : ℝ)*
            ((L/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε))+
          (2*C*Real.sqrt (H*(M : ℝ))/G)*(harmonic (Nat.ceil (L/G)) : ℝ) := by
  classical
  obtain ⟨η,hη,C,hC,hbound⟩ := hpair.atkinson_prefixGramMax_bound hε
  refine ⟨η,hη,C,hC,?_⟩
  intro H G L t M W hH hG hM hsep ht hrange hdiam hsmall
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hR : 0 < Real.sqrt (H*(M : ℝ)) := by positivity
  have hL : 0 ≤ L := by simpa using hdiam t ht
  let S := W.erase t
  let X := (L/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε)
  have hSW : S ⊆ W := Finset.erase_subset _ _
  have hpoint : ∀ u ∈ S, atkinsonPrefixGramMax M M t u ≤
      C*X+(C*Real.sqrt (H*(M : ℝ)))*(1/|u-t|) := by
    intro u hu
    have hne : t ≠ u := (Finset.mem_erase.mp hu).1.symm
    have hb := hbound H t u M hH hM (hrange t ht).1 (hrange t ht).2
      (hrange u (hSW hu)).1 (hrange u (hSW hu)).2 hne hsmall
    have hp : (|t-u|/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε) ≤ X := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hMp.le _)
      apply Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hdiam u (hSW hu)) hR.le)
        (by linarith [hpair.inTriangle.1])
    calc
      _ ≤ C*(X+Real.sqrt (H*(M : ℝ))/|t-u|) :=
        hb.trans (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) (by linarith))
      _ = _ := by rw [abs_sub_comm t u]; ring
  have hrecip : (∑ u ∈ S, 1/|u-t|) ≤
      (2/G)*(harmonic (Nat.ceil (L/G)) : ℝ) :=
    atkinson_sum_inv_gap_le_harmonic_ceil hG hsep ht hSW
      (fun u hu => ⟨(Finset.mem_erase.mp hu).1,hdiam u (hSW hu)⟩)
  have hcard : (S.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hSW
  have hsum : (∑ u ∈ S, atkinsonPrefixGramMax M M t u) ≤
      C*(W.card : ℝ)*X+
        (2*C*Real.sqrt (H*(M : ℝ))/G)*(harmonic (Nat.ceil (L/G)) : ℝ) := calc
    _ ≤ ∑ u ∈ S, (C*X+(C*Real.sqrt (H*(M : ℝ)))*(1/|u-t|)) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ)*(C*X)+(C*Real.sqrt (H*(M : ℝ)))*(∑ u ∈ S, 1/|u-t|) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
    _ ≤ (W.card : ℝ)*(C*X)+(C*Real.sqrt (H*(M : ℝ)))*
        ((2/G)*(harmonic (Nat.ceil (L/G)) : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_right hcard (by dsimp [X]; positivity))
        (mul_le_mul_of_nonneg_left hrecip (by positivity))
    _ = _ := by ring
  rw [← Finset.sum_erase_add _ _ ht,atkinsonPrefixGramMax_self]
  change (∑ u ∈ S, atkinsonPrefixGramMax M M t u)+(M : ℝ) ≤ _
  dsimp [X] at hsum
  linarith


theorem ExponentPair.atkinson_pair_gram_double_sum {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H G L : ℝ) (M : ℕ) (W : Finset ℝ),
        0 < H → 0 < G → 0 < M → IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) → Real.pi*(M : ℝ)/(2*H) < η →
        (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) ≤
          (W.card : ℝ)*(M : ℝ)+C*(W.card : ℝ)^2*
            ((L/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε))+
          (2*C*Real.sqrt (H*(M : ℝ))/G)*(W.card : ℝ)*
            (harmonic (Nat.ceil (L/G)) : ℝ) := by
  obtain ⟨η,hη,C,hC,hrow⟩ := hpair.atkinson_pair_gram_row hε
  refine ⟨η,hη,C,hC,?_⟩
  intro H G L M W hH hG hM hsep hrange hdiam hsmall
  calc
    _ ≤ ∑ _t ∈ W, ((M : ℝ)+C*(W.card : ℝ)*
        ((L/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε))+
        (2*C*Real.sqrt (H*(M : ℝ))/G)*(harmonic (Nat.ceil (L/G)) : ℝ)) :=
      Finset.sum_le_sum (fun t ht => hrow H G L t M W
        hH hG hM hsep ht hrange (hdiam t ht) hsmall)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem ExponentPair.atkinson_phase_packet_pair_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H G L : ℝ) (M : ℕ) (W : Finset ℝ),
        0 < H → 0 < G → 0 < M → IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) → Real.pi*(M : ℝ)/(2*H) < η →
        (∑ t ∈ W, atkinsonPhaseBlockMax t M M)^2 ≤
          atkinsonBlockCoefficientEnergy M M*
            ((W.card : ℝ)*(M : ℝ)+C*(W.card : ℝ)^2*
              ((L/Real.sqrt (H*(M : ℝ)))^(k+ε)*(M : ℝ)^(l+ε))+
            (2*C*Real.sqrt (H*(M : ℝ))/G)*(W.card : ℝ)*
              (harmonic (Nat.ceil (L/G)) : ℝ)) := by
  obtain ⟨η,hη,C,hC,hgram⟩ := hpair.atkinson_pair_gram_double_sum hε
  refine ⟨η,hη,C,hC,?_⟩
  intro H G L M W hH hG hM hsep hrange hdiam hsmall
  exact (sum_atkinsonPhaseBlockMax_sq_le_gramMax M M W).trans
    (mul_le_mul_of_nonneg_left
      (hgram H G L M W hH hG hM hsep hrange hdiam hsmall)
      (atkinsonBlockCoefficientEnergy_nonneg M M))

end TaoTrudgianYang2025
