import TaoTrudgianYang2025.LargeValueSharpGram
import TaoTrudgianYang2025.ZetaIntervalProbe
import TaoTrudgianYang2025.AtkinsonSeparatedReciprocal

/-! Actual near-difference Gram rows, retaining the diagonal and harmonic loss. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem LargeValuePattern.sharp_gram_near_row (P : LargeValuePattern)
    {t L : ℝ} (ht : t ∈ P.ordinates) (hL : 0 ≤ L) (hLN : L ≤ P.N^2) :
    (∑ u ∈ {u ∈ P.ordinates | |u-t| ≤ L},
      ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖) ≤
      2*P.N+(P.ordinates.card : ℝ)*(2+200*Real.sqrt L)+
        24*Real.pi*P.N*(harmonic (Nat.ceil L) : ℝ) := by
  classical
  let A := {u ∈ P.ordinates | |u-t| ≤ L}
  let S := A.erase t
  have htA : t ∈ A := by simp only [A,Finset.mem_filter,ht,sub_self,abs_zero,true_and]; exact hL
  have hSW : S ⊆ P.ordinates := by
    intro u hu
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).1
  have hnear (u : ℝ) (hu : u ∈ S) : u ≠ t ∧ |u-t| ≤ L :=
    ⟨(Finset.mem_erase.mp hu).1,(Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).2⟩
  have hN : 1 < P.scale := by
    have hh := P.one_lt_N
    rw [P.N_eq_scale] at hh
    exact_mod_cast hh
  have hI : IsIntegerInterval P.indices := ⟨P.scale,2*P.scale,P.indices_eq_dyadicInterval⟩
  have hIN : P.indices ⊆ Finset.Icc P.scale (2*P.scale) := by
    rw [P.indices_eq_dyadicInterval]
  have hpoint (u : ℝ) (hu : u ∈ S) :
      ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ ≤
        (2+200*Real.sqrt L)+(12*Real.pi*P.N)*(1/|u-t|) := by
    have hd := hnear u hu
    have hone : 1 ≤ |u-t| := P.ordinates_oneSeparated u (hSW hu) t ht hd.1
    have hh := norm_zetaInterval_le_short_majorant P.scale P.indices |u-t| hN hI hIN hone
      (by rw [← P.N_eq_scale]; exact hd.2.trans hLN)
    rw [← P.N_eq_scale] at hh
    rw [← norm_sum_dirichletPhase_abs P.indices (fun n hn => P.index_pos hn) (u-t)]
    apply hh.trans
    have hs := Real.sqrt_le_sqrt hd.2
    have he : 12*Real.pi*P.N/|u-t| = (12*Real.pi*P.N)*(1/|u-t|) := by ring
    rw [he]
    linarith
  have hrecip : (∑ u ∈ S, 1/|u-t|) ≤ 2*(harmonic (Nat.ceil L) : ℝ) := by
    simpa only [div_one] using atkinson_sum_inv_gap_le_harmonic_ceil
      (G:=1) (by norm_num) P.ordinates_oneSeparated ht hSW hnear
  have hScard : (S.card : ℝ) ≤ P.ordinates.card := by
    exact_mod_cast Finset.card_le_card hSW
  have hcoeff : 0 ≤ 12*Real.pi*P.N := by have := P.one_lt_N; positivity
  have hsum : (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖) ≤
      (P.ordinates.card : ℝ)*(2+200*Real.sqrt L)+
        24*Real.pi*P.N*(harmonic (Nat.ceil L) : ℝ) := calc
    _ ≤ ∑ u ∈ S, ((2+200*Real.sqrt L)+(12*Real.pi*P.N)*(1/|u-t|)) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ)*(2+200*Real.sqrt L)+(12*Real.pi*P.N)*(∑ u ∈ S, 1/|u-t|) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
      ring
    _ ≤ (P.ordinates.card : ℝ)*(2+200*Real.sqrt L)+
        (12*Real.pi*P.N)*(2*(harmonic (Nat.ceil L) : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_right hScard (by positivity))
        (mul_le_mul_of_nonneg_left hrecip hcoeff)
    _ = _ := by ring
  have hdiag : ‖∑ n ∈ P.indices, dirichletPhase n (t-t)‖ ≤ 2*P.N := by
    simpa only [sub_self,dirichletPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast] using P.indices_card_cast_le_two_mul_N
  change (∑ u ∈ A, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖) ≤ _
  rw [← Finset.sum_erase_add _ _ htA]
  change (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖)+
    ‖∑ n ∈ P.indices, dirichletPhase n (t-t)‖ ≤ _
  linarith

end TaoTrudgianYang2025
