import TaoTrudgianYang2025.ZetaSharpReflectionEntry
import TaoTrudgianYang2025.ZetaReciprocalCompletion

/-! A single actual positive frequency annulus contains every moving dual interval. -/

noncomputable section
open Complex MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaReflectionCommonInterval (T N : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.floor (T/(4*Real.pi*N))+1) (Nat.ceil (T/(Real.pi*N)))

theorem zetaReflectionCommonInterval_positive (T N : ℝ) {n : ℕ}
    (hn : n ∈ zetaReflectionCommonInterval T N) : 0 < n := by
  have := (Finset.mem_Icc.mp hn).1
  omega

theorem zetaReflectionCommonInterval_window {T N : ℝ}
    (hT : 0 ≤ T) (hN : 0 < N) {n : ℕ}
    (hn : n ∈ zetaReflectionCommonInterval T N) :
    T/(4*Real.pi*N) < (n : ℝ) ∧ (n : ℝ) ≤ Nat.ceil (T/(Real.pi*N)) := by
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hn
  constructor
  · exact (Nat.floor_lt (by positivity)).1 (by omega)
  · exact_mod_cast hr

theorem logarithmic_moving_interval_subset_common {T N t : ℝ}
    (hT : 0 < T) (hN : 0 < N) (ht : T ≤ t) (ht' : t ≤ 2*T)
    {J : Finset ℕ}
    (hJ : ∀ n ∈ J, t/(4*Real.pi*N) < (n : ℝ) ∧ (n : ℝ) < t/(2*Real.pi*N)) :
    J ⊆ zetaReflectionCommonInterval T N := by
  intro n hn
  obtain ⟨hl,hr⟩ := hJ n hn
  have hlo : T/(4*Real.pi*N) < (n : ℝ) :=
    (div_le_div_of_nonneg_right ht (by positivity)).trans_lt hl
  have hhi : (n : ℝ) ≤ T/(Real.pi*N) := by
    have hu := div_le_div_of_nonneg_right ht' (show 0 ≤ 2*Real.pi*N by positivity)
    have he : 2*T/(2*Real.pi*N) = T/(Real.pi*N) := by field_simp
    rw [he] at hu
    exact hr.le.trans hu
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.succ_le_iff.mpr ((Nat.floor_lt (by positivity)).2 hlo)
  · exact_mod_cast hhi.trans (Nat.le_ceil _)

theorem IsIntegerInterval.positive_endpoints {J : Finset ℕ}
    (hJ : IsIntegerInterval J) (hpos : ∀ n ∈ J, 0 < n) :
    ∃ a b : ℕ, 1 ≤ a ∧ J = Finset.Icc a b := by
  obtain ⟨a,b,hab⟩ := hJ
  refine ⟨max 1 a,b,le_max_left _ _,?_⟩
  ext n
  rw [Finset.mem_Icc]
  constructor
  · intro hn
    have hp := hpos n hn
    rw [hab,Finset.mem_Icc] at hn
    omega
  · intro hn
    rw [hab,Finset.mem_Icc]
    omega

theorem moving_reciprocal_interval_eq_common_mellin {T N t : ℝ}
    (hT : 0 < T) (hN : 0 < N) (ht : T ≤ t) (ht' : t ≤ 2*T)
    {J : Finset ℕ} (hJ : IsIntegerInterval J)
    (hw : ∀ n ∈ J, t/(4*Real.pi*N) < (n : ℝ) ∧ (n : ℝ) < t/(2*Real.pi*N)) :
    ∃ a b : ℕ, 1 ≤ a ∧ J = Finset.Icc a b ∧
      (∑ n ∈ J, (n : ℂ)⁻¹*dirichletPhase n t) =
        (1/(2*Real.pi) : ℂ)*∫ u : ℝ,
          mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
            ∑ n ∈ zetaReflectionCommonInterval T N, dirichletPhase n (t+u) := by
  have hsub := logarithmic_moving_interval_subset_common hT hN ht ht' hw
  obtain ⟨a,b,ha,hint⟩ := hJ.positive_endpoints (fun n hn =>
    zetaReflectionCommonInterval_positive T N (hsub hn))
  refine ⟨a,b,ha,hint,?_⟩
  rw [hint]
  exact reciprocal_interval_eq_common_mellin ha _ (fun n hn =>
    ne_of_gt (zetaReflectionCommonInterval_positive T N hn)) (hint ▸ hsub) t

end TaoTrudgianYang2025
