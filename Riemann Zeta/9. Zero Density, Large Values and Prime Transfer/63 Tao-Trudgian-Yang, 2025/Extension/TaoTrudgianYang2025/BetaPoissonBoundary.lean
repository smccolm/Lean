import TaoTrudgianYang2025.BetaFourierModes

/-!
# Closed source intervals enter Poisson with at most two endpoint terms

A constructed cutoff agrees with every strict-interior lattice point.
The discarded set is proved to lie in the two original endpoints.
Thus the literal source exponential sum differs from an absolutely
convergent Poisson series by a quantity of norm at most two.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

def modelPhaseInteriorIndices (N : ℝ) (a b : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc a b).filter (fun n => N < (n : ℝ) ∧ (n : ℝ) < 2*N)

theorem modelPhaseInteriorIndices_subset (N : ℝ) (a b : ℤ) :
    modelPhaseInteriorIndices N a b ⊆ Finset.Icc a b := by
  classical
  exact Finset.filter_subset _ _

theorem exists_modelPhase_interior_cutoff {N : ℝ} (hN : 0 < N) (a b : ℤ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0 := by
  classical
  let S := modelPhaseInteriorIndices N a b
  by_cases hS : S.Nonempty
  · let l := S.min' hS
    let r := S.max' hS
    have hl := Finset.mem_filter.mp (S.min'_mem hS)
    have hr := Finset.mem_filter.mp (S.max'_mem hS)
    have heq : Finset.Icc l r = S := by
      ext n
      constructor
      · intro hn
        have hn' := Finset.mem_Icc.mp hn
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hl.1).1.trans hn'.1,
            hn'.2.trans (Finset.mem_Icc.mp hr.1).2⟩,?_⟩
        exact ⟨hl.2.1.trans_le (by exact_mod_cast hn'.1),
          (show (n : ℝ) ≤ (r : ℝ) by exact_mod_cast hn'.2).trans_lt hr.2.2⟩
      · intro hn
        exact Finset.mem_Icc.mpr ⟨S.min'_le n hn,S.le_max' n hn⟩
    obtain ⟨χ,hχ,hs,hcompact,hrange,hvalues⟩ :=
      exists_modelPhase_integer_cutoff hN hl.2.1 (S.min'_le_max' hS) hr.2.2
    refine ⟨χ,hχ,hs,hcompact,hrange,?_⟩
    intro n
    change χ ((n : ℝ)/N) = if n ∈ S then 1 else 0
    rw [← heq]
    exact hvalues n
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨fun _ => 0,contDiff_const,?_,?_,by intro x; norm_num,?_⟩
    · simp
    · exact HasCompactSupport.zero
    · intro n
      change (0 : ℝ) = if n ∈ S then 1 else 0
      simp only [he,Finset.notMem_empty,if_false]

theorem modelPhase_boundary_indices_card_le_two
    {N : ℝ} {a b : ℤ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ((Finset.Icc a b) \ modelPhaseInteriorIndices N a b).card ≤ 2 := by
  classical
  have hsub : (Finset.Icc a b) \ modelPhaseInteriorIndices N a b ⊆ {a,b} := by
    intro n hn
    have h := Finset.mem_sdiff.mp hn
    have hnI := Finset.mem_Icc.mp h.1
    have hleft : N ≤ (n : ℝ) := ha.trans (by exact_mod_cast hnI.1)
    have hright : (n : ℝ) ≤ 2*N := (show (n : ℝ) ≤ (b : ℝ) by
      exact_mod_cast hnI.2).trans hb
    have hbad : (n : ℝ) ≤ N ∨ 2*N ≤ (n : ℝ) := by
      simpa only [modelPhaseInteriorIndices,Finset.mem_filter,h.1,true_and,not_and_or,not_lt]
        using h.2
    rcases hbad with hn | hn
    · have hna : n = a := by
        apply le_antisymm _ hnI.1
        exact_mod_cast (hn.trans ha)
      simp only [hna,Finset.mem_insert,Finset.mem_singleton,true_or]
    · have hnb : n = b := by
        apply le_antisymm hnI.2
        exact_mod_cast (hb.trans hn)
      simp only [hnb,Finset.mem_insert,Finset.mem_singleton,or_true]
  exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_le_two])

theorem norm_modelPhase_full_sub_interior_le_two
    (F : ℝ → ℝ) (T : ℝ) {N : ℝ} {a b : ℤ}
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖(∑ n ∈ Finset.Icc a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ)) -
      ∑ n ∈ modelPhaseInteriorIndices N a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ)‖ ≤ 2 := by
  classical
  have hsum := Finset.sum_sdiff (modelPhaseInteriorIndices_subset N a b)
    (f := fun n : ℤ => (𝐞 (T*F ((n : ℝ)/N)) : ℂ))
  rw [← hsum,add_sub_cancel_right]
  calc
    ‖∑ n ∈ (Finset.Icc a b) \ modelPhaseInteriorIndices N a b,
        (𝐞 (T*F ((n : ℝ)/N)) : ℂ)‖ ≤
      ∑ n ∈ (Finset.Icc a b) \ modelPhaseInteriorIndices N a b,
        ‖(𝐞 (T*F ((n : ℝ)/N)) : ℂ)‖ := norm_sum_le _ _
    _ = (((Finset.Icc a b) \ modelPhaseInteriorIndices N a b).card : ℝ) := by
      simp only [Circle.norm_coe,Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ 2 := by exact_mod_cast modelPhase_boundary_indices_card_le_two ha hb

theorem modelPhase_closed_interval_poisson
    {F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ T : ℝ, Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
        ‖exponentialSumAt F T N a b -
          ∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 := by
  classical
  obtain ⟨χ,hχ,hs,hcompact,_,hvalues⟩ := exists_modelPhase_interior_cutoff hN a b
  refine ⟨χ,hχ,hs,hcompact,hvalues,?_⟩
  intro T
  refine ⟨summable_norm_modelPhaseFourierMode hχ hs hF hN T,?_⟩
  have hsource : (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n) =
      ∑ n ∈ modelPhaseInteriorIndices N a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ) := by
    rw [tsum_eq_sum (s := modelPhaseInteriorIndices N a b) (fun n hn => by
      simp only [modelPhaseWeightedKernel,hvalues n,if_neg hn,Complex.ofReal_zero,zero_mul])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [modelPhaseWeightedKernel,hvalues n,if_pos hn,Complex.ofReal_one,one_mul]
  rw [← modelPhase_weighted_poisson hχ hs hF hN T,
    ← modelPhaseWeightedKernel_tsum_eq_finite hs hN T,hsource,exponentialSumAt_eq_int_sum]
  exact norm_modelPhase_full_sub_interior_le_two F T
    (by exact_mod_cast ha) (by exact_mod_cast hb)

end TaoTrudgianYang2025
