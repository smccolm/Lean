import TaoTrudgianYang2025.SargosModelRemainderJets

/-! Closed-interval iterated derivative calculus for the actual transformed model phase. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargos_iteratedDerivWithin_comp_order (i j : ℕ) (f : ℝ → ℝ) (s : Set ℝ) :
    iteratedDerivWithin i (iteratedDerivWithin j f s) s = iteratedDerivWithin (i+j) f s := by
  ext x
  simp only [iteratedDerivWithin_eq_iterate,Function.iterate_add_apply]
  rw [show iteratedDerivWithin j f s = (fun g : ℝ → ℝ => derivWithin g s)^[j] f from
    funext (fun y => iteratedDerivWithin_eq_iterate)]

theorem sargos_contDiffOn_iteratedDerivWithin {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDerivWithin n f s) s := by
  induction n with
  | zero => simpa only [iteratedDerivWithin_zero] using hf
  | succ n hn =>
      rw [iteratedDerivWithin_succ]
      exact hn.derivWithin hs (by simp)

theorem sargos_descPochhammer_four (σ : ℝ) :
    (descPochhammer ℝ 4).eval (-σ) = σ*(σ+1)*(σ+2)*(σ+3) := by
  norm_num [descPochhammer_succ_eval]
  ring

theorem sargos_modelPhaseJetCoefficient_four {σ : ℝ} (hσ : 0 ≤ σ) :
    modelPhaseJetCoefficient σ 4 = σ*(σ+1)*(σ+2)*(σ+3) := by
  rw [modelPhaseJetCoefficient,sargos_descPochhammer_four,abs_of_nonneg (by positivity)]

theorem sargos_descPochhammer_shift_four {σ : ℝ} (hσ : 0 ≤ σ) (p : ℕ) :
    (descPochhammer ℝ (p+4)).eval (-σ) =
      modelPhaseJetCoefficient σ 4*(descPochhammer ℝ p).eval (-(σ+4)) := by
  have h := congrArg (fun P : Polynomial ℝ => P.eval (-σ)) (descPochhammer_mul ℝ 4 p)
  simp only [Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_natCast] at h
  rw [Nat.add_comm 4 p] at h
  rw [sargos_modelPhaseJetCoefficient_four hσ,← sargos_descPochhammer_four]
  rw [show -(σ+4) = -σ-(4:ℝ) by ring]
  exact h.symm

end TaoTrudgianYang2025
