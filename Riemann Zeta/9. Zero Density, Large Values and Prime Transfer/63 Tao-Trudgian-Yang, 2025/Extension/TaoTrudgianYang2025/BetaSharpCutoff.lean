import TaoTrudgianYang2025.BetaModelPoisson

/-!
# Smooth cutoffs agreeing exactly with an interior integer interval

Strict physical endpoint margins permit a smooth plateau with transitions
in lattice gaps. Its values on all scaled integers are the exact interval
indicator. No smoothing error or replacement-sum assumption is introduced.
Derivative bounds uniform in the margins remain a separate obligation.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem exists_modelPhase_integer_cutoff {N : ℝ} (hN : 0 < N)
    {a b : ℤ} (ha : N < (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) < 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ n : ℤ, χ ((n : ℝ)/N) = if n ∈ Finset.Icc a b then 1 else 0 := by
  classical
  let l := max 1 (((a : ℝ)-1)/N)
  let r := min 2 (((b : ℝ)+1)/N)
  have hla : l < (a : ℝ)/N := by
    apply max_lt
    · exact (one_lt_div hN).mpr ha
    · exact (div_lt_div_iff_of_pos_right hN).mpr (by linarith)
  have hbr : (b : ℝ)/N < r := by
    apply lt_min
    · exact (div_lt_iff₀ hN).mpr hb
    · exact (div_lt_div_iff_of_pos_right hN).mpr (by linarith)
  have hab' : (a : ℝ)/N ≤ (b : ℝ)/N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hab) hN.le
  obtain ⟨χ,hχ,hplateau,hs,hcompact,hrange⟩ := exists_smooth_interval_cutoff hla hab' hbr
  refine ⟨χ,hχ,?_,hcompact,hrange,?_⟩
  · intro x hx
    exact ⟨(le_max_left _ _).trans_lt (hs hx).1,
      (hs hx).2.trans_le (min_le_left _ _)⟩
  · intro n
    by_cases hn : n ∈ Finset.Icc a b
    · rw [if_pos hn]
      have h := Finset.mem_Icc.mp hn
      exact hplateau _ ⟨div_le_div_of_nonneg_right (by exact_mod_cast h.1) hN.le,
        div_le_div_of_nonneg_right (by exact_mod_cast h.2) hN.le⟩
    · rw [if_neg hn]
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hu := hs hx
      have hout : n < a ∨ b < n := by
        simpa only [Finset.mem_Icc,not_and_or,not_le] using hn
      rcases hout with hn | hn
      · have hna : (n : ℝ) ≤ (a : ℝ)-1 := by
          exact_mod_cast (show n ≤ a-1 by omega)
        have hnl : (n : ℝ)/N ≤ l :=
          (div_le_div_of_nonneg_right hna hN.le).trans (le_max_right _ _)
        exact (not_lt_of_ge hnl) hu.1
      · have hbn : (b : ℝ)+1 ≤ (n : ℝ) := by
          exact_mod_cast (show b+1 ≤ n by omega)
        have hrn : r ≤ (n : ℝ)/N :=
          (min_le_right _ _).trans (div_le_div_of_nonneg_right hbn hN.le)
        exact (not_lt_of_ge hrn) hu.2

theorem exponentialSumAt_eq_int_sum (F : ℝ → ℝ) (T N : ℝ) (a b : ℕ) :
    exponentialSumAt F T N a b =
      ∑ n ∈ Finset.Icc (a : ℤ) (b : ℤ), (𝐞 (T*F ((n : ℝ)/N)) : ℂ) := by
  classical
  unfold exponentialSumAt oscillatory
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩
  · intro n _ m _ h
    exact_mod_cast h
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    have hn₀ : 0 ≤ n := (Int.natCast_nonneg a).trans h.1
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg hn₀⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n _
    simp only [Int.cast_natCast]

theorem modelPhase_sharp_interval_poisson
    {F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N)
    {a b : ℕ} (ha : N < (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) < 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) = if n ∈ Finset.Icc (a : ℤ) (b : ℤ) then 1 else 0) ∧
      ∀ T : ℝ, exponentialSumAt F T N a b =
        ∑' r : ℤ, modelPhaseFourierMode χ F T N r := by
  classical
  obtain ⟨χ,hχ,hs,hcompact,_,hvalues⟩ := exists_modelPhase_integer_cutoff hN
    (by exact_mod_cast ha : N < ((a : ℤ) : ℝ))
    (by exact_mod_cast hab : (a : ℤ) ≤ (b : ℤ))
    (by exact_mod_cast hb : ((b : ℤ) : ℝ) < 2*N)
  refine ⟨χ,hχ,hs,hcompact,hvalues,?_⟩
  intro T
  have hsource : (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n) =
      exponentialSumAt F T N a b := by
    rw [exponentialSumAt_eq_int_sum]
    rw [tsum_eq_sum (s := Finset.Icc (a : ℤ) (b : ℤ)) (fun n hn => by
      simp only [modelPhaseWeightedKernel,hvalues n,if_neg hn,Complex.ofReal_zero,zero_mul])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [modelPhaseWeightedKernel,hvalues n,if_pos hn,Complex.ofReal_one,one_mul]
  rw [← hsource,modelPhaseWeightedKernel_tsum_eq_finite hs hN T]
  exact modelPhase_weighted_poisson hχ hs hF hN T

end TaoTrudgianYang2025
