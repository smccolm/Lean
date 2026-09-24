import TaoTrudgianYang2025.ZetaIntervalFarMoment
import TaoTrudgianYang2025.LargeValueSharpGram

/-! The far twelfth moment on the actual signed differences of a source pattern. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_sharp_gram_far_twelfth {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ (P : LargeValuePattern) (t : ℝ),
      T₀ ≤ P.T → t ∈ P.ordinates →
      (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ |u-t|},
        ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖^12) ≤ C*P.N^6*P.T^(2+ε) := by
  classical
  obtain ⟨D,T₀,hD,hT₀,hbound⟩ := exists_sum_zetaInterval_far_twelfth_bound hε
  refine ⟨2*D,T₀,by positivity,hT₀,?_⟩
  intro P t hPT ht
  have hN : 1 < P.scale := by
    have hh := P.one_lt_N
    rw [P.N_eq_scale] at hh
    exact_mod_cast hh
  have hI : IsIntegerInterval P.indices := ⟨P.scale,2*P.scale,P.indices_eq_dyadicInterval⟩
  have hIN : P.indices ⊆ Finset.Icc P.scale (2*P.scale) := by
    rw [P.indices_eq_dyadicInterval]
  have hdiff (u : ℝ) (hu : u ∈ P.ordinates) : |u-t| ≤ P.T := by
    have hb := P.ordinates_in_interval u hu
    have ht' := P.ordinates_in_interval t ht
    have hlen := P.interval_length
    apply abs_le.mpr
    constructor <;> linarith
  let f := fun u => ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖^12
  have hsigned (s : ℝ) (hs : |s| = 1) :
      (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ s*(u-t)}, f u) ≤
        D*P.N^6*P.T^(2+ε) := by
    let S := {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ s*(u-t)}
    let X := S.image (fun u => s*(u-t))
    have hsne : s ≠ 0 := by intro he; rw [he,abs_zero] at hs; norm_num at hs
    have hinj : Function.Injective (fun u : ℝ => s*(u-t)) := by
      intro u v he
      have hd := mul_left_cancel₀ hsne he
      linarith
    have hsep : IsOneSeparated X := by
      intro x hx y hy hne
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      have huv : u ≠ v := fun he => hne (by rw [he])
      have hb := P.ordinates_oneSeparated u (Finset.mem_filter.mp hu).1
        v (Finset.mem_filter.mp hv).1 huv
      have he : s*(u-t)-s*(v-t) = s*(u-v) := by ring
      rw [he,abs_mul,hs,one_mul]
      exact hb
    have hX (x : ℝ) (hx : x ∈ X) :
        (P.scale : ℝ)^(11/8 : ℝ) ≤ x ∧ x ≤ P.T := by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      have hb := Finset.mem_filter.mp hu
      refine ⟨by simpa only [P.N_eq_scale] using hb.2,?_⟩
      calc
        s*(u-t) ≤ |s*(u-t)| := le_abs_self _
        _ = |u-t| := by rw [abs_mul,hs,one_mul]
        _ ≤ P.T := hdiff u hb.1
    have hm := hbound P.scale P.indices P.T X hN hI hIN hPT hsep hX
    have heq : (∑ x ∈ X, ‖∑ n ∈ P.indices, dirichletPhase n x‖^12) =
        ∑ u ∈ S, f u := by
      dsimp only [X]
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [f]
      congr 1
      calc
        ‖∑ n ∈ P.indices, dirichletPhase n (s*(u-t))‖ =
            ‖∑ n ∈ P.indices, dirichletPhase n |s*(u-t)|‖ :=
          (norm_sum_dirichletPhase_abs P.indices (fun n hn => P.index_pos hn) _).symm
        _ = ‖∑ n ∈ P.indices, dirichletPhase n |u-t|‖ := by rw [abs_mul,hs,one_mul]
        _ = _ := norm_sum_dirichletPhase_abs P.indices (fun n hn => P.index_pos hn) _
    rw [heq,← P.N_eq_scale] at hm
    exact hm
  have hp := hsigned 1 (by norm_num)
  have hm := hsigned (-1) (by norm_num)
  have hcover : (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ |u-t|}, f u) ≤
      (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ 1*(u-t)}, f u)+
      (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ (-1)*(u-t)}, f u) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    have hf : 0 ≤ f u := by dsimp [f]; positivity
    by_cases hfar : P.N^(11/8 : ℝ) ≤ |u-t|
    · rw [if_pos hfar]
      rcases le_total 0 (u-t) with h | h
      · have hpos : P.N^(11/8 : ℝ) ≤ 1*(u-t) := by
          simpa only [abs_of_nonneg h,one_mul] using hfar
        rw [if_pos hpos]
        split_ifs <;> linarith
      · have hneg : P.N^(11/8 : ℝ) ≤ (-1)*(u-t) := by
          simpa only [abs_of_nonpos h,neg_one_mul] using hfar
        rw [if_pos hneg]
        split_ifs <;> linarith
    · rw [if_neg hfar]
      split_ifs <;> linarith
  change (∑ u ∈ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ |u-t|}, f u) ≤ _
  nlinarith

end TaoTrudgianYang2025

