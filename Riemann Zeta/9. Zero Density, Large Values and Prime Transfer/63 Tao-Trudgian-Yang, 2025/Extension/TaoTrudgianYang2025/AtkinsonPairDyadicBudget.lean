import TaoTrudgianYang2025.AtkinsonPairPowerAlgebra

/-! Removal of actual phase sums and divisor energies from the dyadic budget. -/

noncomputable section
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ExponentPair.atkinson_pair_nominal_gram {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H G L : ℝ) (M : ℕ) (W : Finset ℝ),
        1 ≤ H → 0 < G → 0 < L → L ≤ H → 0 < M → (M : ℝ) ≤ H →
        IsSeparated G W → (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) → Real.pi*(M : ℝ)/(2*H) < η →
        (M : ℝ)^(1/2:ℝ)*
          (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) ≤
          H^(2*ε)*atkinsonPairPowerTerm C k l H G L M W.card := by
  obtain ⟨η,hη,C,hC,hgram⟩ := hpair.atkinson_pair_gram_double_sum hε
  refine ⟨η,hη,C,hC,?_⟩
  intro H G L M W hH hG hL hLH hM hMH hsep hrange hdiam hsmall
  have hH0 : 0 < H := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hb := hgram H G L M W hH0 hG hM hsep hrange hdiam hsmall
  let X := (L/Real.sqrt (H*(M : ℝ)))^k*(M : ℝ)^l
  let B := (2*C*Real.sqrt (H*(M : ℝ))/G)*(W.card : ℝ)*
    (harmonic (Nat.ceil (L/G)) : ℝ)
  have hE : 1 ≤ H^(2*ε) := Real.one_le_rpow hH (by positivity)
  have hB : 0 ≤ B := by
    have hh : (0 : ℝ) ≤ (harmonic (Nat.ceil (L/G)) : ℝ) := by
      simpa only [harmonic_zero,Rat.cast_zero] using
        atkinson_harmonic_mono (Nat.zero_le (Nat.ceil (L/G)))
    dsimp [B]
    positivity
  have hdiag : 0 ≤ (W.card : ℝ)*(M : ℝ) := by positivity
  have hf := mul_le_mul_of_nonneg_left
    (atkinson_pair_epsilon_loss (k := k) (l := l) hH hM1 hMH hL hLH hε.le)
    (by positivity : 0 ≤ C*(W.card : ℝ)^2)
  have hsum : (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) ≤
      H^(2*ε)*((W.card : ℝ)*(M : ℝ)+C*(W.card : ℝ)^2*X+B) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hE) hdiag
    have h2 := mul_nonneg (sub_nonneg.mpr hE) hB
    dsimp [X,B] at *
    nlinarith
  have hw := mul_le_mul_of_nonneg_left hsum
    (Real.rpow_nonneg (Nat.cast_nonneg M) (1/2:ℝ))
  calc
    _ ≤ (M : ℝ)^(1/2:ℝ)*
        (H^(2*ε)*((W.card : ℝ)*(M : ℝ)+C*(W.card : ℝ)^2*X+B)) := hw
    _ = H^(2*ε)*((M : ℝ)^(1/2:ℝ)*
        ((W.card : ℝ)*(M : ℝ)+C*(W.card : ℝ)^2*X+B)) := by ring
    _ = _ := by
      dsimp [X,B]
      rw [atkinson_pair_power_term_eq hH0 hM hL.le]

theorem ExponentPair.atkinson_dyadic_gram_le_pair_budget {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (H G L : ℝ) (N : ℕ) (W : Finset ℝ),
        1 ≤ H → 0 < G → 0 < L → L ≤ H → (N : ℝ) ≤ H →
        IsSeparated G W → (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) → Real.pi*(N : ℝ)/(2*H) < η →
        atkinsonDyadicGramBudget N W ≤
          D*H^(3*ε)*atkinsonPairPowerBudget C k l H G L N W.card := by
  obtain ⟨η,hη,C,hC,hgram⟩ := hpair.atkinson_pair_nominal_gram hε
  obtain ⟨D,hD,henergy⟩ := exists_atkinsonBlockCoefficientEnergy_le hε
  refine ⟨η,hη,C,hC,D,hD,?_⟩
  intro H G L N W hH hG hL hLH hNH hsep hrange hdiam hsmall
  have hH0 : 0 < H := by linarith
  have hp : 0 ≤ l+1/2-k/2 := by
    rcases hpair.inTriangle with ⟨_,hk,hl,_,_⟩
    linarith
  have heps : H^ε*H^(2*ε) = H^(3*ε) := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  unfold atkinsonDyadicGramBudget atkinsonPairPowerBudget
  have hs : (∑ j ∈ Finset.range (Nat.clog 2 N),
      (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
        ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax (2^j) (2^j) t u) ≤
      ∑ _j ∈ Finset.range (Nat.clog 2 N),
        D*H^(3*ε)*atkinsonPairPowerTerm C k l H G L N W.card := by
    apply Finset.sum_le_sum
    intro j hj
    let M : ℕ := 2^j
    have hM : 0 < M := pow_pos (by norm_num) _
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hMN : M ≤ N := (truncatedDyadic_start_lt (Finset.mem_range.mp hj)).le
    have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hMH : (M : ℝ) ≤ H := hMNR.trans hNH
    have hms : Real.pi*(M : ℝ)/(2*H) < η :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMNR Real.pi_pos.le) (by positivity)).trans_lt hsmall
    have hg := hgram H G L M W hH hG hL hLH hM hMH hsep hrange hdiam hms
    have he := henergy M M hM le_rfl
    have hS : 0 ≤ ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u :=
      Finset.sum_nonneg (fun t _ => Finset.sum_nonneg
        (fun u _ => atkinsonPrefixGramMax_nonneg M M t u))
    have hMp := Real.rpow_le_rpow hM0.le hMH hε.le
    have ht := atkinsonPairPowerTerm_mono_index W.card
      (by linarith : 0 ≤ C) hH0.le hG.le hL.le hp hMN
    have hm : ((M : ℝ)^(-(1/4:ℝ)))^2*(M : ℝ)^(1+ε) =
        (M : ℝ)^ε*(M : ℝ)^(1/2:ℝ) := by
      rw [atkinson_quarter_energy_power hM0,← Real.rpow_add hM0]
      congr 1
      ring
    change ((M : ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy M M*
      (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) ≤ _
    calc
      _ ≤ ((M : ℝ)^(-(1/4:ℝ)))^2*(D*(M : ℝ)^(1+ε))*
          (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (sq_nonneg _)) hS
      _ = D*(M : ℝ)^ε*((M : ℝ)^(1/2:ℝ)*
          (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u)) := by
        calc
          _ = D*(((M : ℝ)^(-(1/4:ℝ)))^2*(M : ℝ)^(1+ε))*
              (∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax M M t u) := by ring
          _ = _ := by rw [hm]; ring
      _ ≤ D*(M : ℝ)^ε*(H^(2*ε)*atkinsonPairPowerTerm C k l H G L M W.card) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ D*H^ε*(H^(2*ε)*atkinsonPairPowerTerm C k l H G L N W.card) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hMp hD.le)
          (mul_le_mul_of_nonneg_left ht (by positivity))
          (mul_nonneg (by positivity)
            (atkinsonPairPowerTerm_nonneg (by linarith) hH0.le hG.le hL.le k l M W.card))
          (by positivity)
      _ = _ := by rw [mul_assoc D (H^ε),← mul_assoc (H^ε),heps]; ring
  have hb := mul_le_mul_of_nonneg_left hs
    (Nat.cast_nonneg (Nat.clog 2 N) : (0 : ℝ) ≤ _)
  exact hb.trans_eq (by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring)

end TaoTrudgianYang2025
