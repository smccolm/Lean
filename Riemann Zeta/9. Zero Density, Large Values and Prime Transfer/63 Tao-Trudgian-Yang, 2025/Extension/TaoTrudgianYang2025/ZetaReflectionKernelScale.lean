import TaoTrudgianYang2025.ZetaReciprocalCompletionTails

/-! Uniform geometric constants on the actual reflected annulus. -/

noncomputable section
open Complex MeasureTheory Set
namespace TaoTrudgianYang2025

theorem zetaReflectionCommonInterval_card_bound {T N : ℝ}
    (hT : 0 ≤ T) (hN : 0 < N) (hscale : 1 ≤ T/(4*Real.pi*N)) :
    ((zetaReflectionCommonInterval T N).card : ℝ) ≤ 6*(T/(4*Real.pi*N)) := by
  have hcard : (zetaReflectionCommonInterval T N).card ≤ Nat.ceil (T/(Real.pi*N))+1 := by
    unfold zetaReflectionCommonInterval
    rw [Nat.card_Icc]
    omega
  have hc : ((zetaReflectionCommonInterval T N).card : ℝ) ≤
      (Nat.ceil (T/(Real.pi*N)) : ℝ)+1 := by exact_mod_cast hcard
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ T/(Real.pi*N) by positivity)
  have he : T/(Real.pi*N) = 4*(T/(4*Real.pi*N)) := by field_simp
  rw [he] at hceil hc
  linarith

theorem cutoff_negative_mellin_annulus_bound {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {M : ℝ} (hM : 1 ≤ M)
    (hleft : M < (a : ℝ)) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)‖ ≤
      4*zetaCutoffDerivativeMass 1/(M*(1+|u|)) := by
  have hmass := zetaCutoffDerivativeMass_nonneg 1
  have hden : 0 < M/2 := by linarith
  have hhalf : M/2 ≤ (a : ℝ)-1/2 := by linarith
  calc
    _ ≤ (2*zetaCutoffDerivativeMass 1/((a : ℝ)-1/2))/(1+|u|) :=
      cutoff_negative_mellin_bound ha hab u
    _ ≤ (2*zetaCutoffDerivativeMass 1/(M/2))/(1+|u|) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) hden hhalf
    _ = _ := by field_simp; ring

theorem moving_interval_cutoff_endpoints {T N t : ℝ}
    (hT : 0 < T) (hN : 0 < N) (ht : T ≤ t) (ht' : t ≤ 2*T)
    {J : Finset ℕ} (hJ : IsIntegerInterval J) (hne : J.Nonempty)
    (hw : ∀ n ∈ J, t/(4*Real.pi*N) < (n : ℝ) ∧ (n : ℝ) < t/(2*Real.pi*N)) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ b ∧ J = Finset.Icc a b ∧
      T/(4*Real.pi*N) < (a : ℝ) ∧ (b : ℝ) < T/(Real.pi*N) := by
  have hsub := logarithmic_moving_interval_subset_common hT hN ht ht' hw
  obtain ⟨a,b,ha,hint⟩ := hJ.positive_endpoints (fun n hn =>
    zetaReflectionCommonInterval_positive T N (hsub hn))
  have hab : a ≤ b := Finset.nonempty_Icc.mp (hint ▸ hne)
  have haJ : a ∈ J := by rw [hint]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
  have hbJ : b ∈ J := by rw [hint]; exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  refine ⟨a,b,ha,hab,hint,?_,?_⟩
  · exact (div_le_div_of_nonneg_right ht (by positivity)).trans_lt (hw a haJ).1
  · have hu := div_le_div_of_nonneg_right ht' (show 0 ≤ 2*Real.pi*N by positivity)
    have he : 2*T/(2*Real.pi*N) = T/(Real.pi*N) := by field_simp
    rw [he] at hu
    exact (hw b hbJ).2.trans_le hu

end TaoTrudgianYang2025
