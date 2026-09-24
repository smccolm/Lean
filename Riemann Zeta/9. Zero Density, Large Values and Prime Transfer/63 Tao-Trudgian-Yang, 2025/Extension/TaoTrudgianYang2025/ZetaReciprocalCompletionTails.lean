import TaoTrudgianYang2025.ZetaReflectionCompletionEntry
import TaoTrudgianYang2025.ZetaMellinOrderTails

/-! Arbitrary-order tails of the actual finite common-frequency convolution. -/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem reciprocalCompletion_phase_sum_norm_le_card (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (v : ℝ) :
    ‖∑ n ∈ S, dirichletPhase n v‖ ≤ (S.card : ℝ) := by
  calc
    _ ≤ ∑ n ∈ S, ‖dirichletPhase n v‖ := norm_sum_le _ _
    _ = _ := by
      have hphase : ∀ n ∈ S, ‖dirichletPhase n v‖ = 1 := by
        intro n hn
        simpa [dirichletPhase] using Complex.norm_natCast_cpow_of_pos
          (Nat.pos_of_ne_zero (hS n hn)) (-(I*(v : ℂ)))
      simp only [Finset.sum_congr rfl hphase,Finset.sum_const,nsmul_eq_mul,mul_one]

theorem reciprocalCompletion_integrand_high_order {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) (j : ℕ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
        ∑ n ∈ S, dirichletPhase n (t+u)‖ ≤
      ((S.card : ℝ)*((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2))*
        |u|^(-((j : ℝ)+2)) := by
  rw [norm_mul]
  calc
    _ ≤ (((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2)/|u|^(j+2))*(S.card : ℝ) :=
      mul_le_mul (cutoff_negative_mellin_high_order ha hab hu j)
        (reciprocalCompletion_phase_sum_norm_le_card S hS (t+u))
        (norm_nonneg _) (by have := zetaCutoffDerivativeMass_nonneg (j+2); positivity)
    _ = _ := by
      rw [Real.rpow_neg (abs_nonneg u)]
      have hcast : (j : ℝ)+2 = ((j+2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast,Real.rpow_natCast]
      ring

theorem reciprocalCompletion_tail_integral {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (t : ℝ) {H : ℝ} (hH : 0 < H) (j : ℕ) {E : Set ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ (Icc (-H) H)ᶜ) :
    ‖∫ u : ℝ in E,
      mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
        ∑ n ∈ S, dirichletPhase n (t+u)‖ ≤
      2*(S.card : ℝ)*((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2)/
        (((j : ℝ)+1)*H^(j+1)) := by
  let C : ℝ := (S.card : ℝ)*((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := zetaCutoffDerivativeMass_nonneg (j+2)
    positivity
  have hneg : -((j : ℝ)+2) < -1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have htail : IntegrableOn (fun u : ℝ => C*|u|^(-((j : ℝ)+2))) (Icc (-H) H)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc hneg hH).const_mul C
  have hi := integrable_reciprocal_completion_kernel (zetaIntervalCutoffTest a b ha) S hS t
  calc
    _ ≤ ∫ u : ℝ in E,
        ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
          ∑ n ∈ S, dirichletPhase n (t+u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in E, C*|u|^(-((j : ℝ)+2)) := by
      apply integral_mono_ae hi.norm.integrableOn (htail.mono_set hsub)
      filter_upwards [ae_restrict_mem hE] with u hu
      have hne : u ≠ 0 := by
        intro h
        subst u
        exact hsub hu ⟨by linarith, hH.le⟩
      exact reciprocalCompletion_integrand_high_order ha hab S hS t hne j
    _ ≤ ∫ u : ℝ in (Icc (-H) H)ᶜ, C*|u|^(-((j : ℝ)+2)) :=
      setIntegral_mono_set htail (Eventually.of_forall fun u =>
        mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)) (Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_const_mul,integral_abs_rpow_compl_Icc hneg hH]
      have he : -((j : ℝ)+2)+1 = -((j+1 : ℕ) : ℝ) := by push_cast; ring
      rw [he,Real.rpow_neg hH.le,Real.rpow_natCast]
      dsimp [C]
      push_cast
      field_simp

end TaoTrudgianYang2025
