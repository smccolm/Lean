import TaoTrudgianYang2025.IvicSixthGramRow

/-! Finite cardinality from the actual restricted-sixth smooth Gram row. -/

noncomputable section
open Finset MeasureTheory
namespace TaoTrudgianYang2025

theorem ivicSixth_gram_absorption {R N V C S E : ℝ} (hR : 0 ≤ R)
    (hrow : R*V^2 ≤ 2*N*C*(4*N+Real.sqrt N*S+R*Real.sqrt N*E))
    (hsmall : 4*C*N*Real.sqrt N*E ≤ V^2) :
    R*V^2 ≤ 32*C*N^2 ∨ R*V^2 ≤ 8*C*N*Real.sqrt N*S := by
  have hm := mul_le_mul_of_nonneg_left hsmall hR
  by_cases hs : R*V^2 ≤ 32*C*N^2
  · exact Or.inl hs
  right
  have hl := lt_of_not_ge hs
  nlinarith [hrow,hm]

theorem exists_ivicSixth_gram_cardinality {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, ∀ H U : ℝ, 0 ≤ H →
      4*C*P.N*Real.sqrt P.N*(2*H*U+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ 32*C*P.N^2 ∨
      (P.ordinates.card:ℝ)*P.V^12 ≤
        (8*C)^6*P.N^9*(2*H)^5*(2*H+1)*
          (∫ v in -(P.T+H)..P.T+H,ivicSixthExcess U v^6) := by
  obtain ⟨C,hC,hrow⟩ := exists_ivicSixth_gram_row_split hq
  refine ⟨C,hC,?_⟩
  intro P H U hH hsmall
  by_cases hne : P.ordinates.Nonempty
  swap
  · left
    have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  obtain ⟨t,ht,hrow⟩ := hrow P hne H U hH
  let R : ℝ := P.ordinates.card
  let S : ℝ := ∑ u ∈ P.ordinates, ∫ v in -H..H,ivicSixthExcess U (u-t+v)
  let E : ℝ := 2*H*U+(1+P.T)/(1+H)^(2*q)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast hne.card_pos
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hg : R*P.V^2 ≤ 2*P.N*C*(4*P.N+Real.sqrt P.N*S+R*Real.sqrt P.N*E) := by
    convert hrow using 1
    dsimp [R,S,E]
    ring
  rcases ivicSixth_gram_absorption hR.le hg hsmall with hd | hm
  · exact Or.inl hd
  right
  have hs0 (u : ℝ) : 0 ≤ ∫ v in -H..H,ivicSixthExcess U (u-t+v) :=
    intervalIntegral.integral_nonneg (by linarith) (fun v _ => ivicSixthExcess_nonneg _ _)
  have hh := pow_sum_le_card_mul_sum_pow (s := P.ordinates)
    (f := fun u => ∫ v in -H..H,ivicSixthExcess U (u-t+v))
    (fun u _ => hs0 u) 5
  norm_num only [Nat.reduceAdd] at hh
  have hw := P.ivicSixth_difference_window_sixth ht hH U
  have hsum : S^6 ≤ R^5*((2*H)^5*(2*H+1)*
      (∫ v in -(P.T+H)..P.T+H,ivicSixthExcess U v^6)) :=
    hh.trans (mul_le_mul_of_nonneg_left hw (pow_nonneg hR.le _))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R*P.V^2) hm 6
  have hscale : (8*C*P.N*Real.sqrt P.N)^6 = (8*C)^6*P.N^9 := by
    have hs : Real.sqrt P.N^6 = P.N^3 := by
      calc
        _ = (Real.sqrt P.N^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hN.le]
    rw [mul_pow,mul_pow,hs]
    ring
  have hleft : (R*P.V^2)^6 = R^5*(R*P.V^12) := by ring
  rw [hleft,mul_pow,hscale] at hp
  have hb := hp.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  apply (mul_le_mul_iff_right₀ (pow_pos hR 5)).mp
  convert hb using 1
  ring

end TaoTrudgianYang2025
