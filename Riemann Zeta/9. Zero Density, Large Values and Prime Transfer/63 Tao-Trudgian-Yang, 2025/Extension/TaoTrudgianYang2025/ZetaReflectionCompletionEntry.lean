import TaoTrudgianYang2025.ZetaReflectionCommonInterval

/-! Actual-pattern reflection into one common coefficient-one convolution. -/

noncomputable section
open Complex MeasureTheory Set
namespace TaoTrudgianYang2025

theorem zetaPattern_common_mellin_reflection_entry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, 2*Real.pi ≤ P.T →
      ∀ t ∈ P.ordinates, ∃ a b : ℕ, 1 ≤ a ∧
        Integrable (fun u : ℝ =>
          mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
            ∑ n ∈ zetaReflectionCommonInterval P.T P.N, dirichletPhase n (t+u)) ∧
        P.V ≤ Real.sqrt (t/(2*Real.pi))*
          ‖(1/(2*Real.pi) : ℂ)*∫ u : ℝ,
            mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
              ∑ n ∈ zetaReflectionCommonInterval P.T P.N, dirichletPhase n (t+u)‖+
          C*(P.N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hentry⟩ := zetaPattern_sharp_log_reflection_entry hε
  refine ⟨C,hC,?_⟩
  intro P hPT t ht
  obtain ⟨c,d,_,hsource⟩ := hentry P hPT
  obtain ⟨hint,hw,hbound⟩ := hsource t ht
  have htime : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  obtain ⟨a,b,ha,_,hid⟩ := moving_reciprocal_interval_eq_common_mellin
    P.T_pos (zero_lt_one.trans P.one_lt_N) htime.1 htime.2 hint hw
  refine ⟨a,b,ha,integrable_reciprocal_completion_kernel (zetaIntervalCutoffTest a b ha) _
    (fun n hn => ne_of_gt (zetaReflectionCommonInterval_positive P.T P.N hn)) t,?_⟩
  rwa [hid] at hbound

end TaoTrudgianYang2025
