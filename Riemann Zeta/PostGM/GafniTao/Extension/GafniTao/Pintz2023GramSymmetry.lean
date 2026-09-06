import GafniTao.Pintz2023SmoothedZeta

/-!
# Conjugation symmetry of Pintz's smoothed Gram series

The small-`B_h` estimate is naturally stated for a positive frequency.
This file proves the exact passage from a signed zero-ordinate difference
to its absolute value.  It uses that every coefficient of the smoothed
Dirichlet series is real; no symmetry is assumed as an external hypothesis.
-/

open Complex

namespace GafniTao

noncomputable section

theorem conj_pintz2023SmoothedZetaTerm
    (N n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) (pintz2023SmoothedZetaTerm N s n) =
      pintz2023SmoothedZetaTerm N ((starRingEnd ℂ) s) n := by
  by_cases hn : n = 0
  · simp [pintz2023SmoothedZetaTerm, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      simp
      exact ne_of_lt Real.pi_pos
    unfold pintz2023SmoothedZetaTerm
    rw [if_neg hn, if_neg hn]
    change (starRingEnd ℂ)
        (((pintz2023HalaszKernel N n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) = _
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    have hcpow := Complex.conj_cpow
      (n : ℂ) (-((starRingEnd ℂ) s)) harg
    simpa using hcpow.symm

theorem norm_pintz2023SmoothedZetaSum_neg_im
    (N : ℕ) (a t : ℝ) :
    ‖pintz2023SmoothedZetaSum N ((a : ℂ) + I * (t : ℂ))‖ =
      ‖pintz2023SmoothedZetaSum N
        ((a : ℂ) + I * ((-t : ℝ) : ℂ))‖ := by
  have hconj : (starRingEnd ℂ)
      (pintz2023SmoothedZetaSum N
        ((a : ℂ) + I * ((-t : ℝ) : ℂ))) =
      pintz2023SmoothedZetaSum N ((a : ℂ) + I * (t : ℂ)) := by
    unfold pintz2023SmoothedZetaSum
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    rw [conj_pintz2023SmoothedZetaTerm]
    congr 2
    apply Complex.ext <;> simp
  calc
    _ = ‖(starRingEnd ℂ)
        (pintz2023SmoothedZetaSum N
          ((a : ℂ) + I * ((-t : ℝ) : ℂ)))‖ := by rw [hconj]
    _ = _ := Complex.norm_conj _

theorem norm_pintz2023SmoothedZetaSum_abs_im
    (N : ℕ) (a t : ℝ) :
    ‖pintz2023SmoothedZetaSum N ((a : ℂ) + I * (t : ℂ))‖ =
      ‖pintz2023SmoothedZetaSum N ((a : ℂ) + I * ((|t| : ℝ) : ℂ))‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht']
    exact norm_pintz2023SmoothedZetaSum_neg_im N a t

#print axioms conj_pintz2023SmoothedZetaTerm
#print axioms norm_pintz2023SmoothedZetaSum_abs_im

end

end GafniTao
