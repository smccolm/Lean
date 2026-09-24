import TaoTrudgianYang2025.ZetaMellinEntry
import TaoTrudgianYang2025.ZetaMellinNegativeUniform

/-!
# Exact finite completion of reciprocal Dirichlet intervals

Mellin inversion on real line -1 cancels the reciprocal coefficient.
The common finite frequency set is retained literally, and every
sum/integral interchange has its integrability proof.
-/

noncomputable section
open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem reciprocal_zetaMellinTerm {n : ℕ} (hn : n ≠ 0)
    (g : ℝ → ℂ) (t u : ℝ) :
    (n : ℂ)⁻¹*zetaMellinTerm g (-1) t n u =
      mellin g ((-1 : ℂ)+(u : ℂ)*I)*dirichletPhase n (t+u) := by
  have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold zetaMellinTerm
  rw [LSeries.term_of_ne_zero hn]
  simp only [Pi.one_apply,one_div,← cpow_neg,ofReal_neg,ofReal_one]
  have he : -((-1 : ℂ)+((u+t : ℝ) : ℂ)*I) = 1+(-(I*((t+u : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [he,cpow_add _ _ hbase,cpow_one]
  unfold dirichletPhase
  field_simp
  simp only [cpow_eq_pow,mul_comm]

theorem integrable_reciprocal_completion_kernel {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (t : ℝ) :
    Integrable (fun u : ℝ => mellin g ((-1 : ℂ)+(u : ℂ)*I)*
      ∑ n ∈ S, dirichletPhase n (t+u)) := by
  have h : Integrable (fun u : ℝ => ∑ n ∈ S, (n : ℂ)⁻¹*zetaMellinTerm g (-1) t n u) :=
    integrable_finsetSum S (fun n _ => (integrable_zetaMellinTerm hg (-1) t n).const_mul _)
  apply h.congr
  filter_upwards with u
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n hn => reciprocal_zetaMellinTerm (hS n hn) g t u)

theorem smooth_reciprocal_sum_eq_common_mellin {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (t : ℝ) :
    (∑ n ∈ S, g n*((n : ℂ)⁻¹*dirichletPhase n t)) =
      (1/(2*Real.pi) : ℂ)*∫ u : ℝ,
        mellin g ((-1 : ℂ)+(u : ℂ)*I)*∑ n ∈ S, dirichletPhase n (t+u) := by
  calc
    _ = ∑ n ∈ S, (1/(2*Real.pi) : ℂ)*∫ u : ℝ,
        (n : ℂ)⁻¹*zetaMellinTerm g (-1) t n u := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_const_mul]
      calc
        _ = (n : ℂ)⁻¹*(g n*dirichletPhase n t) := by ring
        _ = _ := by rw [← integral_zetaMellinTerm_eq hg (-1) t n]; ring
    _ = (1/(2*Real.pi) : ℂ)*∫ u : ℝ,
        ∑ n ∈ S, (n : ℂ)⁻¹*zetaMellinTerm g (-1) t n u := by
      rw [integral_finsetSum S (fun n _ => (integrable_zetaMellinTerm hg (-1) t n).const_mul _),
        Finset.mul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n hn => reciprocal_zetaMellinTerm (hS n hn) g t u)

theorem reciprocal_interval_eq_common_mellin {a b : ℕ} (ha : 1 ≤ a)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (hsub : Finset.Icc a b ⊆ S) (t : ℝ) :
    (∑ n ∈ Finset.Icc a b, (n : ℂ)⁻¹*dirichletPhase n t) =
      (1/(2*Real.pi) : ℂ)*∫ u : ℝ,
        mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
          ∑ n ∈ S, dirichletPhase n (t+u) := by
  rw [← smooth_reciprocal_sum_eq_common_mellin (zetaIntervalCutoffTest a b ha) S hS t]
  symm
  calc
    _ = ∑ n ∈ Finset.Icc a b, (zetaIntervalCutoff a b n : ℂ)*((n : ℂ)⁻¹*dirichletPhase n t) :=
      (Finset.sum_subset hsub (fun n _ hn => by simp [zetaIntervalCutoff_nat,hn])).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [zetaIntervalCutoff_nat,if_pos hn,ofReal_one,one_mul]

end TaoTrudgianYang2025
