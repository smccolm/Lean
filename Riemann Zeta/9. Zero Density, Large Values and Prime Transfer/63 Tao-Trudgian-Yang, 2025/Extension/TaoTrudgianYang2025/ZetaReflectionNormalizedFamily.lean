import TaoTrudgianYang2025.ZetaReflectionHeightBlocks
import TaoTrudgianYang2025.ZetaReflectionScaleBounds

/-! Genuine normalized zeta patterns built from literal reflected frequency and height blocks. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem exists_zetaIntervalFamilyPattern (m : ℕ) (S : Finset ℕ) (T A : ℝ)
    (hm : 1 < m) (hS : IsIntegerInterval S)
    (hsub : S ⊆ Finset.Icc m (2*m)) (hT : 0 < T) (hA : 0 < A)
    (W : Finset ℝ) (hsep : IsOneSeparated W)
    (hheight : ∀ t ∈ W, t ∈ Icc T (2*T))
    (hlarge : ∀ t ∈ W, A ≤ ‖∑ n ∈ S, dirichletPhase n t‖) :
    ∃ P : ZetaLargeValuePattern, P.N = (m : ℝ) ∧ P.T = T ∧
      P.V = A ∧ P.active = S ∧ P.ordinates = W := by
  have heval (t : ℝ) : (∑ n ∈ Finset.Icc m (2*m),
      (if n ∈ S then (1 : ℂ) else 0)*dirichletPhase n t) =
      ∑ n ∈ S, dirichletPhase n t := by
    simp only [ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hsub]
  let P : ZetaLargeValuePattern := {
    N := m
    scale := m
    T := T
    V := A
    coeff := fun n => if n ∈ S then 1 else 0
    indices := Finset.Icc m (2*m)
    intervalLeft := T
    intervalRight := 2*T
    ordinates := W
    N_eq_scale := rfl
    one_lt_N := by exact_mod_cast hm
    T_pos := hT
    V_pos := hA
    mem_indices_iff := by intro n; simp only [Finset.mem_Icc]; norm_cast
    coeff_one_bounded := by intro n _; split_ifs <;> norm_num
    interval_length := by ring
    ordinates_in_interval := hheight
    ordinates_oneSeparated := hsep
    large := by intro t ht; rw [heval]; exact hlarge t ht
    active := S
    active_isInterval := hS
    active_subset := hsub
    coeff_eq_indicator := fun _ _ => rfl
    intervalLeft_eq := rfl
    intervalRight_eq := rfl }
  exact ⟨P,rfl,rfl,rfl,rfl,rfl⟩

theorem exists_reflection_normalized_family {M T A : ℝ}
    (hM : 4 ≤ M) (hT : 0 < T) (hA : 0 < A)
    (W : Finset ℝ) (hne : W.Nonempty) (hsep : IsOneSeparated W)
    (hheight : ∀ t ∈ W, t ∈ Icc (T/2) (3*T))
    (hlarge : ∀ t ∈ W,
      A ≤ ‖∑ n ∈ Finset.Icc (Nat.floor M+1) (Nat.ceil (4*M)), dirichletPhase n t‖) :
    ∃ Q : ZetaLargeValuePattern, Q.ordinates.Nonempty ∧ Q.ordinates ⊆ W ∧
      M/2 ≤ Q.N ∧ Q.N ≤ 4*M ∧ T/2 ≤ Q.T ∧ Q.T ≤ 2*T ∧ Q.V = A/3 ∧
      (W.card : ℝ)/9 ≤ (Q.ordinates.card : ℝ) ∧
      A*(W.card : ℝ)/27 ≤ Q.V*(Q.ordinates.card : ℝ) ∧
      ∃ i k : Fin 3, Q.N = ((2^i.val*Nat.floor M : ℕ) : ℝ) ∧
        Q.T = reflectionHeightScale T k ∧
        Q.active = reflectionDyadicBlock (Nat.floor M) (Nat.ceil (4*M)) i := by
  obtain ⟨i,U,hUne,hUsub,hUcard,hUlarge⟩ := exists_reflection_frequency_family
    (reflection_ceil_le_eight_floor hM) W hne A hlarge
  obtain ⟨k,V,hVne,hVsub,hVcard,hVheight⟩ := exists_reflection_height_family hT U hUne
    (fun t ht => hheight t (hUsub ht))
  have hVsep : IsOneSeparated V := fun t ht u hu htu =>
    hsep t (hUsub (hVsub ht)) u (hUsub (hVsub hu)) htu
  obtain ⟨hscale,hlo,hhi⟩ := reflection_dyadic_scale_bounds hM i
  obtain ⟨Q,hQN,hQT,hQV,hQS,hQW⟩ := exists_zetaIntervalFamilyPattern
    (2^i.val*Nat.floor M) (reflectionDyadicBlock (Nat.floor M) (Nat.ceil (4*M)) i)
    (reflectionHeightScale T k) (A/3) hscale ⟨_,_,rfl⟩
    (reflectionDyadicBlock_subset_dyadic _ _ i) (reflectionHeightScale_pos hT k)
    (by positivity) V hVsep hVheight (fun t ht => hUlarge t (hVsub ht))
  obtain ⟨hTlo,hThi⟩ := reflectionHeightScale_bounds hT k
  have hc : (W.card : ℝ)/9 ≤ (V.card : ℝ) := by linarith
  refine ⟨Q,hQW.symm ▸ hVne,?_,hQN.symm ▸ hlo,hQN.symm ▸ hhi,
    hQT.symm ▸ hTlo,hQT.symm ▸ hThi,hQV,?_,?_,i,k,hQN,hQT,hQS⟩
  · rw [hQW]
    exact hVsub.trans hUsub
  · simpa only [hQW] using hc
  · rw [hQV,hQW]
    nlinarith [mul_le_mul_of_nonneg_left hc hA.le]

end TaoTrudgianYang2025
