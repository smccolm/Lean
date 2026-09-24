import TaoTrudgianYang2025.ZetaLowHeightExact
import TaoTrudgianYang2025.ZetaLogarithmicPair
import TaoTrudgianYang2025.ZetaPointwiseNonexistence
import TaoTrudgianYang2025.ExponentPairLowFrequency

/-! First-derivative cancellation gives the exact sharp low-height boundary. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem norm_sum_cpow_neg_im_le_lowHeight {t N : ℝ} (ht : 0 < t)
    (hN : 0 < N) (htN : t ≤ N) (a b : ℕ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤
      (2*Real.pi*modelPhaseFirstDerivativeConstant 1)*(N/t) := by
  rw [norm_sum_cpow_neg_im_eq_logModel hN a b ha t]
  have hp : 0 < 2*Real.pi := by positivity
  have hs : t/(2*Real.pi) ≤ N/4 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [Real.pi_gt_three]
  have he := norm_exponentialSumAt_le_firstDerivative
    (σ:=1) (δ:=0) (by norm_num) (by positivity : 0 < t/(2*Real.pi)) hN
    (le_min (by positivity) zero_le_one)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num : (0 : ℝ) < 1)).le zero_le_one)
    (log_approximateModel 1 (le_refl 0)) ha hb hs
  apply he.trans_eq
  field_simp

theorem zetaLargeValueExponent_eq_bot_of_lowHeight {σ τ : ℝ}
    (hτ : τ < 1) (hσ : 1-τ < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  let δ := min ((1-τ)/2) ((σ-(1-τ))/8)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδh : δ ≤ (1-τ)/2 := min_le_left _ _
  have hδs : δ ≤ (σ-(1-τ))/8 := min_le_right _ _
  let B := 2*Real.pi*modelPhaseFirstDerivativeConstant 1
  have hev : ∀ᶠ N : ℝ in atTop, B ≤ N^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop B)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  apply zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving
  refine ⟨max 2 N₀,δ,(by have := le_max_left (2 : ℝ) N₀; linarith),hδ,?_⟩
  intro N I t hNC hI hsub htlo hthi
  have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans hNC
  have hN1 : (1 : ℝ) < N := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have htp : 0 < t := (Real.rpow_pos_of_pos hNp _).trans_le htlo
  have htN : t ≤ N := calc
    _ ≤ (N : ℝ)^(τ+δ) := hthi
    _ ≤ (N : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
    _ = N := Real.rpow_one _
  have hconst := hN₀ (N : ℝ) ((le_max_right _ _).trans hNC)
  by_cases hIempty : I = ∅
  · subst I
    simpa only [Finset.sum_empty,norm_zero] using
      Real.rpow_pos_of_pos hNp (σ-δ)
  obtain ⟨a,b,rfl⟩ := hI
  have hab : a ≤ b := Finset.nonempty_Icc.mp (Finset.nonempty_iff_ne_empty.mpr hIempty)
  have hNa : N ≤ a := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩))).1
  have hbN : b ≤ 2*N := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩))).2
  have hsum := norm_sum_cpow_neg_im_le_lowHeight htp hNp htN a b
    (by exact_mod_cast hNa) (by exact_mod_cast hbN)
  have hratio : (N : ℝ)/t ≤ (N : ℝ)^(1-τ+δ) := calc
    _ ≤ (N : ℝ)/(N : ℝ)^(τ-δ) :=
      div_le_div_of_nonneg_left hNp.le (Real.rpow_pos_of_pos hNp _) htlo
    _ = (N : ℝ)^(1-τ+δ) := by
      rw [show 1-τ+δ = 1-(τ-δ) by ring,
        Real.rpow_sub hNp 1 (τ-δ),Real.rpow_one]
  have hphase : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      ∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I)) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [dirichletPhase,mul_comm Complex.I (t : ℂ)]
    rfl
  rw [hphase]
  calc
    _ ≤ B*((N : ℝ)/t) := hsum
    _ ≤ (N : ℝ)^δ*(N : ℝ)^(1-τ+δ) :=
      mul_le_mul hconst hratio (div_nonneg hNp.le htp.le)
        (Real.rpow_nonneg hNp.le _)
    _ = (N : ℝ)^(1-τ+2*δ) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    _ < (N : ℝ)^(σ-δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)

theorem zetaLargeValueExponent_lowHeight {σ τ : ℝ}
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    zetaLargeValueExponent σ τ = if σ ≤ 1-τ then (τ : EReal) else ⊥ := by
  split_ifs with h
  · exact zetaLargeValueExponent_eq_tau_of_lowHeight hσ hτ (by linarith)
  · exact zetaLargeValueExponent_eq_bot_of_lowHeight hτ1 (lt_of_not_ge h)

end TaoTrudgianYang2025
