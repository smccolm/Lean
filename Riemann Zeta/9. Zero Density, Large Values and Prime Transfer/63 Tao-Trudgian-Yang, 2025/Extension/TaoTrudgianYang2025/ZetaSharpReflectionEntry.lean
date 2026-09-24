import TaoTrudgianYang2025.ZetaLogDualInterval
import TaoTrudgianYang2025.ZetaIntervalCutoff

/-! Literal zeta-pattern entry into sharp logarithmic reflection. -/

noncomputable section
open Set Complex
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem zetaPattern_sharp_log_reflection_entry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, 2*Real.pi ≤ P.T →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ∀ t ∈ P.ordinates,
          IsIntegerInterval (zetaLogDualInterval (t/(2*Real.pi)) P.N a b) ∧
          (∀ n ∈ zetaLogDualInterval (t/(2*Real.pi)) P.N a b,
            t/(4*Real.pi*P.N) < (n : ℝ) ∧ (n : ℝ) < t/(2*Real.pi*P.N)) ∧
          P.V ≤ Real.sqrt (t/(2*Real.pi))*
            ‖∑ n ∈ zetaLogDualInterval (t/(2*Real.pi)) P.N a b,
              (n : ℂ)⁻¹*dirichletPhase n t‖+
            C*(P.N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hbound⟩ := dirichletInterval_sharp_natural_reflection hε
  refine ⟨C,hC,?_⟩
  intro P hPT
  obtain ⟨a,b,hactive⟩ := P.active_isInterval
  refine ⟨a,b,hactive,?_⟩
  intro t ht
  have hne := P.active_nonempty_of_mem_ordinates ht
  have hb := P.active_interval_bounds hactive hne
  have htime : P.T ≤ t := by
    have hi := (P.ordinates_in_interval t ht).1
    simpa only [P.intervalLeft_eq] using hi
  have hNpos := zero_lt_one.trans P.one_lt_N
  have htp := P.T_pos.trans_le htime
  have hHeightPos : 0 < t/(2*Real.pi) := div_pos htp (by positivity)
  refine ⟨zetaLogDualInterval_isIntegerInterval hHeightPos hNpos hb.2.1 hb.2.2,?_,?_⟩
  · intro n hn
    have hw := zetaLogDualInterval_window hHeightPos hNpos hb.2.1 hb.2.2 hn
    have hlo : t/(2*Real.pi)/(2*P.N) = t/(4*Real.pi*P.N) := by field_simp; norm_num
    have hhi : t/(2*Real.pi)/P.N = t/(2*Real.pi*P.N) := by field_simp
    simpa only [hlo,hhi] using hw
  · have hl := P.large t ht
    rw [P.polynomial_eq_active_sum,hactive] at hl
    exact hl.trans (hbound P.N t a b P.one_lt_N.le (hPT.trans htime) hb.2.1 hb.2.2)

end TaoTrudgianYang2025
