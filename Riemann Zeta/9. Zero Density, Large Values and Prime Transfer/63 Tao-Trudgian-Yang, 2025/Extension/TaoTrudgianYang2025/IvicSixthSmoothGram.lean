import TaoTrudgianYang2025.LargeValueSharpGram
import TaoTrudgianYang2025.ZetaIntervalCutoff

/-! A genuine fixed-profile smooth Gram kernel for every source pattern. -/

noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace TaoTrudgianYang2025

def ivicSixthSmoothTrace (Q : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (3*Q),
    ((zetaIntervalCutoff 1 2 ((n:ℝ)/Q) : ℝ):ℂ)^2*dirichletPhase n t

theorem ivicSixthSmoothTrace_eq_tsum {Q : ℕ} (hQ : 0 < Q) (t : ℝ) :
    ivicSixthSmoothTrace Q t =
      ∑' n : ℕ, ((zetaIntervalCutoff 1 2 ((n:ℝ)/Q) : ℝ):ℂ)^2*
        dirichletPhase n t := by
  symm
  apply tsum_eq_sum
  intro n hn
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  have hz : zetaIntervalCutoff 1 2 ((n:ℝ)/Q) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      apply zetaIntervalCutoff_eq_zero_left
      norm_num
    · have hn' : 3*Q < n := by
        have := mt Finset.mem_Icc.mpr hn
        omega
      apply zetaIntervalCutoff_eq_zero_right
      apply (le_div_iff₀ hQ0).mpr
      have hr : 3*(Q:ℝ) < n := by exact_mod_cast hn'
      norm_num
      linarith
  simp only [hz,ofReal_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul]

theorem LargeValuePattern.smooth_sixth_gram (P : LargeValuePattern) :
    ((P.ordinates.card : ℝ)*P.V)^2 ≤
      2*P.N*∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖ivicSixthSmoothTrace P.scale (u-t)‖ := by
  classical
  let S := Finset.Icc 1 (3*P.scale)
  let a := fun n => if n ∈ P.indices then P.coeff n else 0
  let w := fun n : ℕ => zetaIntervalCutoff 1 2 ((n:ℝ)/P.scale)
  let y := fun t n => (w n:ℂ)*dirichletPhase n t
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hQ : (0:ℝ) < P.scale := by simpa only [P.N_eq_scale] using hN
  have hsub : P.indices ⊆ S := by
    intro n hn
    have hb := Finset.mem_Icc.mp (P.indices_eq_dyadicInterval ▸ hn)
    exact Finset.mem_Icc.mpr ⟨P.index_pos hn,by omega⟩
  have hw (n : ℕ) (hn : n ∈ P.indices) : w n = 1 := by
    obtain ⟨hl,hu⟩ := (P.mem_indices_iff n).mp hn
    dsimp [w]
    apply zetaIntervalCutoff_eq_one
    · apply (le_div_iff₀ hQ).mpr
      simpa only [Nat.cast_one,one_mul,← P.N_eq_scale] using hl
    · apply (div_le_iff₀ hQ).mpr
      simpa only [← P.N_eq_scale] using hu
  have hentry (t : ℝ) : (∑ n ∈ S, a n*y t n) =
      ∑ n ∈ P.indices, P.coeff n*dirichletPhase n t := by
    calc
      _ = ∑ n ∈ P.indices, a n*y t n := by
        symm
        apply Finset.sum_subset hsub
        intro n _ hn
        simp [a,hn]
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [a,y,hn,hw n hn])
  have hcoeff : (∑ n ∈ S, ‖a n‖^2) ≤ 2*P.N := by
    calc
      _ = ∑ n ∈ P.indices, ‖P.coeff n‖^2 := by
        calc
          _ = ∑ n ∈ P.indices, ‖a n‖^2 := by
            symm
            apply Finset.sum_subset hsub
            intro n _ hn
            simp [a,hn]
          _ = _ := Finset.sum_congr rfl (fun n hn => by simp [a,hn])
      _ ≤ ∑ _n ∈ P.indices, (1:ℝ) := Finset.sum_le_sum (fun n hn => by
        simpa only [one_pow] using
          pow_le_pow_left₀ (norm_nonneg _) (P.coeff_one_bounded n hn) 2)
      _ = (P.indices.card:ℝ) := by simp
      _ ≤ _ := P.indices_card_cast_le_two_mul_N
  have hkernel (t u : ℝ) :
      (∑ n ∈ S, conj (y t n)*y u n) = ivicSixthSmoothTrace P.scale (u-t) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    dsimp [y]
    rw [map_mul,Complex.conj_ofReal]
    have hp := dirichletPhase_mul_star hn0 u t
    rw [Complex.star_def] at hp
    calc
      _ = (w n:ℂ)^2*(dirichletPhase n u*conj (dirichletPhase n t)) := by ring
      _ = _ := by rw [hp]
  have hg := finite_sampling_gram S P.ordinates a y P.V_pos.le
    (fun t ht => by rw [hentry]; exact P.large t ht)
  simp only [hkernel] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

theorem LargeValuePattern.exists_large_smooth_sixth_gram_row (P : LargeValuePattern)
    (hne : P.ordinates.Nonempty) :
    ∃ t ∈ P.ordinates, (P.ordinates.card : ℝ)*P.V^2 ≤
      2*P.N*∑ u ∈ P.ordinates, ‖ivicSixthSmoothTrace P.scale (u-t)‖ := by
  let S := fun t => ∑ u ∈ P.ordinates, ‖ivicSixthSmoothTrace P.scale (u-t)‖
  obtain ⟨t,ht,hmax⟩ := P.ordinates.exists_max_image S hne
  have hs : (∑ v ∈ P.ordinates, S v) ≤ (P.ordinates.card:ℝ)*S t := by
    calc
      _ ≤ ∑ _v ∈ P.ordinates, S t := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hg := P.smooth_sixth_gram
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*(∑ v ∈ P.ordinates,S v) at hg
  have hb := hg.trans (mul_le_mul_of_nonneg_left hs (by have := P.one_lt_N; positivity))
  have hR : (0:ℝ) < P.ordinates.card := by exact_mod_cast hne.card_pos
  refine ⟨t,ht,?_⟩
  change (P.ordinates.card:ℝ)*P.V^2 ≤ 2*P.N*S t
  apply (mul_le_mul_iff_right₀ hR).mp
  nlinarith [hb]

end TaoTrudgianYang2025
