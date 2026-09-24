import TaoTrudgianYang2025.DirichletMeanSquareTranslation
import TaoTrudgianYang2025.DirichletBlockPhase

/-!
# Lower mean square of literal coefficient-one Dirichlet blocks

The native mean-square identity retains its diagonal. Its two Hilbert
forms give a two-sided error, hence a genuine lower bound on each
translated interval. No large-value or growth hypothesis is used.
-/

noncomputable section
open Complex MeasureTheory
open scoped Interval ComplexConjugate
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem abs_integral_norm_sq_dirichletTime_sub_diagonal
    (N : ℕ) (T : ℝ) (a : ℕ → ℂ) (hN : 0 < N) :
    |(∫ t : ℝ in 0..T, ‖dirichletTime N a t‖^2) -
      T * ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2| ≤
      2*(5*Real.pi+1)*(N : ℝ) * ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  let S : ℝ := ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2
  have hsum : (∑ n ∈ Finset.Ioc N (2*N), conj (a n)*a n) = (S : ℂ) := by
    dsimp [S]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    exact map_pow Complex.ofRealHom ‖a n‖ 2
  have htwist : ∑ n ∈ Finset.Ioc N (2*N), ‖endpointTwist T a n‖^2 = S := by
    simp only [norm_endpointTwist,S]
  have hcast := ofReal_integral_norm_sq_dirichletTime N T a
  rw [hsum] at hcast
  have hdev :
      (((∫ t : ℝ in 0..T, ‖dirichletTime N a t‖^2) - T*S : ℝ) : ℂ) =
      I*(logHilbertQuad N (endpointTwist T a)-logHilbertQuad N a) := by
    push_cast
    rw [hcast]
    ring
  change |(∫ t : ℝ in 0..T, ‖dirichletTime N a t‖^2)-T*S| ≤
    2*(5*Real.pi+1)*(N : ℝ)*S
  rw [← Real.norm_eq_abs,← Complex.norm_real,hdev,norm_mul,Complex.norm_I,one_mul]
  calc
    _ ≤ ‖logHilbertQuad N (endpointTwist T a)‖+‖logHilbertQuad N a‖ :=
      norm_sub_le _ _
    _ ≤ (5*Real.pi+1)*(N : ℝ)*S+(5*Real.pi+1)*(N : ℝ)*S :=
      add_le_add (by simpa only [htwist] using
        logHilbertQuad_norm_le N (endpointTwist T a) hN)
        (logHilbertQuad_norm_le N a hN)
    _ = _ := by ring

theorem integral_norm_sq_dirichletTime_interval_ge
    (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) (hN : 0 < N) :
    (B-A-2*(5*Real.pi+1)*(N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 ≤
      ∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2 := by
  have h := abs_integral_norm_sq_dirichletTime_sub_diagonal N (B-A)
    (endpointTwist A a) hN
  simp only [norm_endpointTwist] at h
  have heq :
      (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) =
        ∫ t : ℝ in 0..B-A, ‖dirichletTime N (endpointTwist A a) t‖^2 := by
    have ht := intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ‖dirichletTime N a t‖^2) A (a := 0) (b := B-A)
    simpa only [dirichletTime_shift,zero_add,sub_add_cancel] using ht.symm
  rw [heq]
  have hh := (abs_le.mp h).1
  nlinarith

theorem dirichletTime_one_eq_phase_interval (N : ℕ) (t : ℝ) :
    dirichletTime N (fun _ => 1) t =
      ∑ n ∈ Finset.Icc (N+1) (2*N), dirichletPhase n t := by
  have hI : Finset.Ioc N (2*N) = Finset.Icc (N+1) (2*N) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [dirichletTime,hI]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [one_mul,dirichletPhase_eq_exp hnp]
  congr 1
  push_cast
  ring

theorem integral_dirichletPhase_norm_sq_ge
    (N : ℕ) (A B : ℝ) (hN : 0 < N) :
    (B-A-2*(5*Real.pi+1)*(N : ℝ))*(N : ℝ) ≤
      ∫ t : ℝ in A..B,
        ‖∑ n ∈ Finset.Icc (N+1) (2*N), dirichletPhase n t‖^2 := by
  have h := integral_norm_sq_dirichletTime_interval_ge N (fun _ => 1) A B hN
  have hs : (∑ n ∈ Finset.Ioc N (2*N), ‖(1 : ℂ)‖^2) = (N : ℝ) := by
    simp only [norm_one,one_pow,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]
    congr 1
    omega
  simpa only [hs,dirichletTime_one_eq_phase_interval] using h

end TaoTrudgianYang2025
