import TaoTrudgianYang2025.BetaBufferedCutoff
import TaoTrudgianYang2025.BetaPoissonBoundary

/-!
# Controlled boundary loss for the actual source sum

A buffered cutoff need not interpolate every lattice point. The discrepancy
is supported on two endpoint bands, whose total cardinality is bounded
uniformly by 4*N*eta+2. Empty, reversed and singleton intervals are allowed.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

def modelPhaseBufferedBoundary (a b : ℤ) (m : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc a b).filter (fun n => n < a+m ∨ b-m < n)

theorem modelPhaseBufferedBoundary_card_le (a b : ℤ) (m : ℕ) :
    (modelPhaseBufferedBoundary a b m).card ≤ 2*m := by
  classical
  have hs : modelPhaseBufferedBoundary a b m ⊆
      Finset.Ico a (a+m) ∪ Finset.Ioc (b-m) b := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    have hi := Finset.mem_Icc.mp h.1
    rcases h.2 with hl | hr
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Ico.mpr ⟨hi.1,hl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_Ioc.mpr ⟨hr,hi.2⟩))
  apply (Finset.card_le_card hs).trans
  apply (Finset.card_union_le _ _).trans
  simp only [Int.card_Ico,Int.card_Ioc,add_sub_cancel_left,sub_sub_cancel,Int.toNat_natCast]
  omega

theorem modelPhaseBufferedCutoff_one_off_boundary
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η)
    {a b n : ℤ} (hn : n ∈ Finset.Icc a b)
    (hnot : n ∉ modelPhaseBufferedBoundary a b ⌈2*N*η⌉₊) :
    modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η ((n : ℝ)/N) = 1 := by
  classical
  have h : ¬ (n < a+(⌈2*N*η⌉₊ : ℤ) ∨ b-(⌈2*N*η⌉₊ : ℤ) < n) := by
    simpa only [modelPhaseBufferedBoundary,Finset.mem_filter,hn,true_and] using hnot
  have hl : a+(⌈2*N*η⌉₊ : ℤ) ≤ n := le_of_not_gt (fun h' => h (Or.inl h'))
  have hr : n ≤ b-(⌈2*N*η⌉₊ : ℤ) := le_of_not_gt (fun h' => h (Or.inr h'))
  have hl' : (a : ℝ)+(⌈2*N*η⌉₊ : ℝ) ≤ n := by exact_mod_cast hl
  have hr' : (n : ℝ) ≤ (b : ℝ)-(⌈2*N*η⌉₊ : ℝ) := by exact_mod_cast hr
  have hm := Nat.le_ceil (2*N*η)
  apply modelPhaseBufferedCutoff_one hη
  · apply (le_div_iff₀ hN).mpr
    have ha : ((a : ℝ)/N+2*η)*N = a+2*N*η := by field_simp
    rw [ha]
    linarith
  · apply (div_le_iff₀ hN).mpr
    have hb : ((b : ℝ)/N-2*η)*N = b-2*N*η := by field_simp
    rw [hb]
    linarith

theorem modelPhaseBufferedKernel_zero_outside
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η)
    (F : ℝ → ℝ) (T : ℝ) {a b n : ℤ} (hn : n ∉ Finset.Icc a b) :
    modelPhaseWeightedKernel (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η)
      F T N n = 0 := by
  have hout : n < a ∨ b < n := by
    simpa only [Finset.mem_Icc,not_and_or,not_le] using hn
  have hz : modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η ((n : ℝ)/N) = 0 := by
    rcases hout with hl | hr
    · apply modelPhaseBufferedCutoff_zero_left hη
      have h := (div_lt_div_iff_of_pos_right hN).mpr (show (n : ℝ) < a by exact_mod_cast hl)
      linarith
    · apply modelPhaseBufferedCutoff_zero_right hη
      have h := (div_lt_div_iff_of_pos_right hN).mpr (show (b : ℝ) < n by exact_mod_cast hr)
      linarith
  simp only [modelPhaseWeightedKernel,hz,Complex.ofReal_zero,zero_mul]

theorem norm_modelPhase_source_sub_buffered_le
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η) (F : ℝ → ℝ) (T : ℝ) (a b : ℤ) :
    ‖(∑ n ∈ Finset.Icc a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ))-
      ∑' n : ℤ, modelPhaseWeightedKernel
        (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N n‖ ≤ 4*N*η+2 := by
  classical
  let χ := modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
  let S := modelPhaseBufferedBoundary a b ⌈2*N*η⌉₊
  let E : ℤ → ℂ := fun n => (𝐞 (T*F ((n : ℝ)/N)) : ℂ)-
    modelPhaseWeightedKernel χ F T N n
  have hsum : (∑ n ∈ Finset.Icc a b, E n) = ∑ n ∈ S, E n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hχ := modelPhaseBufferedCutoff_one_off_boundary hN hη hn hnot
    simp only [E,modelPhaseWeightedKernel,χ,hχ,Complex.ofReal_one,one_mul,sub_self]
  have hnorm : ∀ n : ℤ, ‖E n‖ ≤ 1 := by
    intro n
    have hχ₀ := modelPhaseBufferedCutoff_nonneg ((a : ℝ)/N) ((b : ℝ)/N) η ((n : ℝ)/N)
    have hχ₁ := modelPhaseBufferedCutoff_le_one ((a : ℝ)/N) ((b : ℝ)/N) η ((n : ℝ)/N)
    have he : E n = ((1-χ ((n : ℝ)/N) : ℝ) : ℂ)*
        (𝐞 (T*F ((n : ℝ)/N)) : ℂ) := by
      simp only [E,modelPhaseWeightedKernel,Complex.ofReal_sub,Complex.ofReal_one]
      ring
    rw [he,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hχ₁)]
    linarith
  rw [tsum_eq_sum (s := Finset.Icc a b)
    (fun n hn => modelPhaseBufferedKernel_zero_outside hN hη F T hn),
    ← Finset.sum_sub_distrib]
  change ‖∑ n ∈ Finset.Icc a b, E n‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ S, ‖E n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hnorm n)
    _ = (S.card : ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ 2*(⌈2*N*η⌉₊ : ℝ) := by exact_mod_cast modelPhaseBufferedBoundary_card_le a b ⌈2*N*η⌉₊
    _ ≤ 4*N*η+2 := by
      have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*N*η)
      linarith

theorem modelPhase_buffered_poisson
    {F : ℝ → ℝ} {σ δ N η : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hN : 0 < N) (hη : 0 < η)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) (T : ℝ) :
    Summable (fun r : ℤ => ‖modelPhaseFourierMode
      (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N r‖) ∧
    ‖exponentialSumAt F T N a b-
      ∑' r : ℤ, modelPhaseFourierMode
        (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N r‖ ≤ 4*N*η+2 := by
  have hs := modelPhaseBufferedCutoff_tsupport_model hη
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb)
  have hχ := modelPhaseBufferedCutoff_contDiff ((a : ℝ)/N) ((b : ℝ)/N) η
  refine ⟨summable_norm_modelPhaseFourierMode hχ hs hF hN T,?_⟩
  rw [← modelPhase_weighted_poisson hχ hs hF hN T,
    ← modelPhaseWeightedKernel_tsum_eq_finite hs hN T,exponentialSumAt_eq_int_sum]
  exact norm_modelPhase_source_sub_buffered_le hN hη F T a b

end TaoTrudgianYang2025
