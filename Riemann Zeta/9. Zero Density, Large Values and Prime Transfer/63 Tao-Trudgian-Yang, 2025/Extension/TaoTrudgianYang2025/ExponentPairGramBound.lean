import TaoTrudgianYang2025.ZetaLogarithmicPair
import TaoTrudgianYang2025.LargeValueSharpGram
import TaoTrudgianYang2025.AtkinsonSeparatedReciprocal

/-!
# Actual sharp Gram estimates from an analytic exponent pair

The low-height N/t term is retained and summed using genuine
one-separation. The diagonal and harmonic loss are not discarded.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem LargeValuePattern.ordinate_gap_le_height (P : LargeValuePattern)
    {t u : ℝ} (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates) :
    |u-t| ≤ P.T := by
  have hti := P.ordinates_in_interval t ht
  have hui := P.ordinates_in_interval u hu
  rw [abs_le]
  constructor <;> linarith [P.interval_length]

theorem ExponentPair.sharp_gram_row_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : LargeValuePattern) (t : ℝ), t ∈ P.ordinates →
      (∑ u ∈ P.ordinates, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖) ≤
        2*P.N+C*(P.ordinates.card : ℝ)*(P.T/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T) : ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hpair.logarithmic_sum_bound hε
  refine ⟨C,hC,?_⟩
  intro P t ht
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  let S := P.ordinates.erase t
  let X := (P.T/P.N)^(k+ε)*P.N^(l+ε)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hSW : S ⊆ P.ordinates := Finset.erase_subset _ _
  have hnear (u : ℝ) (hu : u ∈ S) : u ≠ t ∧ |u-t| ≤ P.T :=
    ⟨(Finset.mem_erase.mp hu).1,P.ordinate_gap_le_height ht (hSW hu)⟩
  have hpoint (u : ℝ) (hu : u ∈ S) :
      ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ ≤
        C*X+(2*Real.pi*C*P.N)*(1/|u-t|) := by
    have hd := hnear u hu
    have hone : 1 ≤ |u-t| :=
      P.ordinates_oneSeparated u (hSW hu) t ht hd.1
    have hh := hbound |u-t| P.N P.scale (2*P.scale)
      (by linarith) P.one_lt_N.le P.N_eq_scale.le
      (by rw [Nat.cast_mul,Nat.cast_ofNat,← P.N_eq_scale])
    have he : (∑ n ∈ P.indices, dirichletPhase n |u-t|) =
        ∑ n ∈ Finset.Icc P.scale (2*P.scale),
          (n : ℂ)^(-(((|u-t| : ℝ) : ℂ)*Complex.I)) := by
      rw [P.indices_eq_dyadicInterval]
      apply Finset.sum_congr rfl
      intro n _
      simp only [dirichletPhase,mul_comm Complex.I]
      rfl
    rw [← he,norm_sum_dirichletPhase_abs P.indices
      (fun n hn => P.index_pos hn) (u-t)] at hh
    have hpow : (|u-t|/P.N)^(k+ε)*P.N^(l+ε) ≤ X := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNp.le _)
      exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right hd.2 hNp.le)
        (by linarith [hpair.inTriangle.1])
    have hs := mul_le_mul_of_nonneg_left
      (add_le_add hpow (le_refl (2*Real.pi*P.N/|u-t|))) (by linarith : 0 ≤ C)
    calc
      _ ≤ C*(X+2*Real.pi*P.N/|u-t|) := hh.trans hs
      _ = _ := by ring
  have hrecip : (∑ u ∈ S, 1/|u-t|) ≤ 2*(harmonic (Nat.ceil P.T) : ℝ) := by
    simpa only [div_one] using atkinson_sum_inv_gap_le_harmonic_ceil
      (G:=1) (by norm_num) P.ordinates_oneSeparated ht hSW hnear
  have hcard : (S.card : ℝ) ≤ P.ordinates.card := by
    exact_mod_cast Finset.card_le_card hSW
  have hsum : (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖) ≤
      C*(P.ordinates.card : ℝ)*X+
        4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T) : ℝ) := calc
    _ ≤ ∑ u ∈ S, (C*X+(2*Real.pi*C*P.N)*(1/|u-t|)) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ)*(C*X)+(2*Real.pi*C*P.N)*(∑ u ∈ S, 1/|u-t|) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
    _ ≤ (P.ordinates.card : ℝ)*(C*X)+
        (2*Real.pi*C*P.N)*(2*(harmonic (Nat.ceil P.T) : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_right hcard (by positivity))
        (mul_le_mul_of_nonneg_left hrecip (by positivity))
    _ = _ := by ring
  have hdiag : ‖∑ n ∈ P.indices, dirichletPhase n (t-t)‖ ≤ 2*P.N := by
    simpa only [sub_self,dirichletPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast] using P.indices_card_cast_le_two_mul_N
  rw [← Finset.sum_erase_add _ _ ht]
  change (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖)+
    ‖∑ n ∈ P.indices, dirichletPhase n (t-t)‖ ≤ _
  dsimp [X] at hsum
  linarith

theorem ExponentPair.sharp_gram_cardinality_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : LargeValuePattern,
      4*C*P.N*(P.T/P.N)^(k+ε)*P.N^(l+ε) ≤ P.V^2 →
      (P.ordinates.card : ℝ)*P.V^2 ≤
        4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T) : ℝ)) := by
  obtain ⟨C,hC,hrow⟩ := hpair.sharp_gram_row_bound hε
  refine ⟨C,hC,?_⟩
  intro P hvalue
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hharm : (0 : ℝ) ≤ harmonic (Nat.ceil P.T) := by
    exact_mod_cast (Finset.sum_nonneg (fun i _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i+1))) : (0 : ℚ) ≤ harmonic (Nat.ceil P.T))
  by_cases hempty : P.ordinates = ∅
  · simpa only [hempty,Finset.card_empty,Nat.cast_zero,zero_mul] using
      (show 0 ≤ 4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T) : ℝ)) by
        positivity)
  have hne := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨t,ht,hgram⟩ := P.exists_large_sharp_gram_row hne
  have hupper := hgram.trans
    (mul_le_mul_of_nonneg_left (hrow P t ht) (by positivity))
  have habsorb := mul_le_mul_of_nonneg_left hvalue (Nat.cast_nonneg P.ordinates.card)
  nlinarith

end TaoTrudgianYang2025
