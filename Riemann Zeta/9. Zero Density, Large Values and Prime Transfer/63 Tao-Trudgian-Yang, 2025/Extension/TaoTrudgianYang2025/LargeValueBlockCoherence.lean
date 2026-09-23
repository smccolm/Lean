import TaoTrudgianYang2025.DirichletBlockPhase
import TaoTrudgianYang2025.LargeValueBlockGeometry

/-! Actual coherent block sums on the full finite short-height range. -/

open Finset

namespace TaoTrudgianYang2025

theorem largeValueBlock_phase_near {N L j : ℕ} (hN : 0 < N) (hL : 0 < L)
    {t : ℝ} (ht : 0 ≤ t) (hheight : t ≤ (N:ℝ)/(2*(L:ℝ)))
    {n : ℕ} (hn : n ∈ largeValueBlock N L j) :
    ‖dirichletPhase n t-dirichletPhase (N+j*L) t‖ ≤ 1/2 := by
  have hp := mem_Ico.mp hn
  have ha : 0 < N+j*L := by omega
  have hap : (0:ℝ) < (N+j*L:ℕ) := by exact_mod_cast ha
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hdiff : (n:ℝ)-((N+j*L:ℕ):ℝ) ≤ (L:ℝ) := by
    have hu : n ≤ N+j*L+L := by
      simp only [Nat.add_mul,Nat.one_mul] at hp
      omega
    have hur : (n:ℝ) ≤ ((N+j*L:ℕ):ℝ)+(L:ℝ) := by exact_mod_cast hu
    linarith
  have hNle : (N:ℝ) ≤ ((N+j*L:ℕ):ℝ) := by exact_mod_cast (Nat.le_add_right N (j*L))
  have htime := (le_div_iff₀ (show (0:ℝ) < 2*L by positivity)).mp hheight
  have hvar := dirichletPhase_block_variation ha hp.1 ht
  apply hvar.trans
  apply (div_le_iff₀ hap).mpr
  have hm := mul_le_mul_of_nonneg_left hdiff ht
  nlinarith

theorem largeValueBlock_sum_lower {N L j : ℕ} (hN : 0 < N) (hL : 0 < L)
    {t : ℝ} (ht : 0 ≤ t) (hheight : t ≤ (N:ℝ)/(2*(L:ℝ))) :
    (L:ℝ)/2 ≤ ‖∑ n ∈ largeValueBlock N L j, dirichletPhase n t‖ := by
  have hphase : ‖dirichletPhase (N+j*L) t‖ = 1 := by
    simpa [dirichletPhase] using Complex.norm_natCast_cpow_of_pos
      (show 0 < N+j*L by omega) (-(Complex.I*(t:ℂ)))
  have hdiff :
      ‖(∑ n ∈ largeValueBlock N L j, dirichletPhase n t)-
        (L:ℂ)*dirichletPhase (N+j*L) t‖ ≤ (L:ℝ)/2 := by
    calc
      _ = ‖∑ n ∈ largeValueBlock N L j,
          (dirichletPhase n t-dirichletPhase (N+j*L) t)‖ := by
        simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,largeValueBlock_card]
      _ ≤ ∑ n ∈ largeValueBlock N L j,
          ‖dirichletPhase n t-dirichletPhase (N+j*L) t‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ largeValueBlock N L j, (1/2:ℝ) :=
        sum_le_sum (fun n hn => largeValueBlock_phase_near hN hL ht hheight hn)
      _ = (L:ℝ)/2 := by simp [largeValueBlock_card,div_eq_mul_inv]
  have href : ‖(L:ℂ)*dirichletPhase (N+j*L) t‖ = (L:ℝ) := by
    rw [norm_mul,hphase,mul_one]
    exact Complex.norm_natCast L
  have hrev := norm_sub_norm_le ((L:ℂ)*dirichletPhase (N+j*L) t)
    (∑ n ∈ largeValueBlock N L j, dirichletPhase n t)
  rw [href,norm_sub_rev] at hrev
  linarith

end TaoTrudgianYang2025

