import TaoTrudgianYang2025.JutilaGram
import TaoTrudgianYang2025.LargeValuePattern

/-! Exact closed-support Gram rows for the actual large-value pattern. -/

noncomputable section
namespace TaoTrudgianYang2025

private theorem dirichletPhase_eq_heathBrown (n : ℕ) (t : ℝ) :
    dirichletPhase n t = RiemannZeta.GuthMaynard.heathBrownPhase n t := by
  unfold dirichletPhase RiemannZeta.GuthMaynard.heathBrownPhase
  congr 1
  ring

theorem dirichletPhase_mul_star {n : ℕ} (hn : 0 < n) (t u : ℝ) :
    dirichletPhase n t*star (dirichletPhase n u) = dirichletPhase n (t-u) := by
  simp only [dirichletPhase_eq_heathBrown]
  exact RiemannZeta.GuthMaynard.heathBrownPhase_mul_star n hn t u

theorem norm_sum_dirichletPhase_abs (I : Finset ℕ)
    (hI : ∀ n ∈ I, 0 < n) (t : ℝ) :
    ‖∑ n ∈ I, dirichletPhase n |t|‖ = ‖∑ n ∈ I, dirichletPhase n t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  rw [abs_of_neg (lt_of_not_ge ht)]
  have he : (∑ n ∈ I, dirichletPhase n (-t)) = star (∑ n ∈ I, dirichletPhase n t) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [dirichletPhase_zero,one_mul,zero_sub] using
      (dirichletPhase_mul_star (hI n hn) 0 t).symm
  rw [he,norm_star]

theorem LargeValuePattern.sharp_gram (P : LargeValuePattern) :
    ((P.ordinates.card : ℝ)*P.V)^2 ≤
      2*P.N*∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ := by
  have h := finite_sampling_gram P.indices P.ordinates P.coeff
    (fun t n => dirichletPhase n t) P.V_pos.le P.large
  have hkernel (t u : ℝ) : (∑ n ∈ P.indices,
      star (dirichletPhase n t)*dirichletPhase n u) =
      ∑ n ∈ P.indices, dirichletPhase n (u-t) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_comm,dirichletPhase_mul_star (P.index_pos hn)]
  simp only [← Complex.star_def,hkernel] at h
  have hcoeff : (∑ n ∈ P.indices, ‖P.coeff n‖^2) ≤ 2*P.N := calc
    _ ≤ ∑ _n ∈ P.indices, (1 : ℝ) :=
      Finset.sum_le_sum fun n hn => by
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (P.coeff_one_bounded n hn) 2
    _ = (P.indices.card : ℝ) := by simp
    _ ≤ 2*P.N := P.indices_card_cast_le_two_mul_N
  exact h.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

theorem LargeValuePattern.exists_large_sharp_gram_row (P : LargeValuePattern)
    (hne : P.ordinates.Nonempty) :
    ∃ t ∈ P.ordinates, (P.ordinates.card : ℝ)*P.V^2 ≤
      2*P.N*∑ u ∈ P.ordinates, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ := by
  let S := fun t => ∑ u ∈ P.ordinates, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖
  obtain ⟨t,ht,hmax⟩ := P.ordinates.exists_max_image S hne
  have hsum : (∑ v ∈ P.ordinates, S v) ≤ (P.ordinates.card : ℝ)*S t := by
    calc
      _ ≤ ∑ _v ∈ P.ordinates, S t := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hg := P.sharp_gram
  change ((P.ordinates.card : ℝ)*P.V)^2 ≤ 2*P.N*(∑ v ∈ P.ordinates, S v) at hg
  have hh := hg.trans (mul_le_mul_of_nonneg_left hsum (by have := P.one_lt_N; positivity))
  have hR : (0 : ℝ) < P.ordinates.card := by exact_mod_cast hne.card_pos
  refine ⟨t,ht,?_⟩
  change (P.ordinates.card : ℝ)*P.V^2 ≤ 2*P.N*S t
  have hfact : (P.ordinates.card : ℝ)*((P.ordinates.card : ℝ)*P.V^2) ≤
      (P.ordinates.card : ℝ)*(2*P.N*S t) := by nlinarith [hh]
  exact (mul_le_mul_iff_right₀ hR).mp hfact

end TaoTrudgianYang2025

