import TaoTrudgianYang2025.ZetaShortPatterns

/-!
# Genuine singleton probes of sharp coefficient-one intervals

The stored positive value is the norm of the actual sum at the sampled
ordinate. The probe transfers existing pattern estimates to literal sums.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_zetaIntervalProbe (N : ℕ) (I : Finset ℕ) (T t : ℝ)
    (hN : 1 < N) (hI : IsIntegerInterval I)
    (hIN : I ⊆ Finset.Icc N (2*N)) (hT : 0 < T)
    (ht : t ∈ Set.Icc T (2*T))
    (hvalue : 0 < ‖∑ n ∈ I, dirichletPhase n t‖) :
    ∃ P : ZetaLargeValuePattern, P.N = (N : ℝ) ∧ P.T = T ∧
      P.active = I ∧ P.V = ‖∑ n ∈ I, dirichletPhase n t‖ ∧ t ∈ P.ordinates := by
  classical
  have heval (u : ℝ) : (∑ n ∈ Finset.Icc N (2*N),
      (if n ∈ I then (1 : ℂ) else 0)*dirichletPhase n u) =
      ∑ n ∈ I, dirichletPhase n u := by
    simp only [ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hIN]
  let P : ZetaLargeValuePattern := {
    N := N
    scale := N
    T := T
    V := ‖∑ n ∈ I, dirichletPhase n t‖
    coeff := fun n => if n ∈ I then 1 else 0
    indices := Finset.Icc N (2*N)
    intervalLeft := T
    intervalRight := 2*T
    ordinates := {t}
    N_eq_scale := rfl
    one_lt_N := by exact_mod_cast hN
    T_pos := hT
    V_pos := hvalue
    mem_indices_iff := by intro n; simp only [Finset.mem_Icc]; norm_cast
    coeff_one_bounded := by intro n _; split_ifs <;> norm_num
    interval_length := by ring
    ordinates_in_interval := by
      intro u hu
      have he := Finset.mem_singleton.mp hu
      subst u
      exact ht
    ordinates_oneSeparated := by
      intro u hu v hv huv
      exact (huv ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm)).elim
    large := by
      intro u hu
      have he := Finset.mem_singleton.mp hu
      subst u
      rw [heval]
    active := I
    active_isInterval := hI
    active_subset := hIN
    coeff_eq_indicator := fun _ _ => rfl
    intervalLeft_eq := rfl
    intervalRight_eq := rfl }
  exact ⟨P,rfl,rfl,rfl,rfl,Finset.mem_singleton_self t⟩

theorem norm_zetaInterval_le_short_majorant
    (N : ℕ) (I : Finset ℕ) (t : ℝ) (hN : 1 < N)
    (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2*N))
    (ht : 1 ≤ t) (htN : t ≤ (N : ℝ)^2) :
    ‖∑ n ∈ I, dirichletPhase n t‖ ≤
      2+200*Real.sqrt t+12*Real.pi*(N : ℝ)/t := by
  by_cases hz : ‖∑ n ∈ I, dirichletPhase n t‖ = 0
  · rw [hz]
    positivity
  have hp : 0 < ‖∑ n ∈ I, dirichletPhase n t‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  obtain ⟨P,hPN,_hPT,hPI,_hPV,_htP⟩ := exists_zetaIntervalProbe N I t t hN hI hIN
    (by linarith) ⟨le_rfl,by linarith⟩ hp
  have hb := P.polynomial_norm_le_short_majorant ht (by simpa only [hPN] using htN)
  simpa only [P.polynomial_eq_active_sum,hPI,hPN] using hb

end TaoTrudgianYang2025
