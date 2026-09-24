import TaoTrudgianYang2025.ZetaPairNonexistenceMargin
import TaoTrudgianYang2025.ClassicalSecondDerivativePair
import TaoTrudgianYang2025.ExponentPairAProcess

/-!
# Pair-to-zeta-large-values transfer with the low-height term retained

The extra condition sigma>1-tau is essential below height N. It is
automatic in the high-height range used by the zero-density applications.
-/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem ExponentPair.zetaLargeValueExponent_eq_bot {k l σ τ : ℝ}
    (h : ExponentPair k l) (hτ : 0 ≤ τ)
    (hmain : k*τ+l-k < σ) (hres : 1-τ < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨δ,hδ,_hδ1,hkδ,ha,hb⟩ :=
    exists_zetaPair_nonexistence_margin h.inTriangle.1 hτ hmain hres
  obtain ⟨B,hB,hbound⟩ := h.logarithmic_sum_bound hδ
  have hev : ∀ᶠ N : ℝ in atTop, B*(1+2*Real.pi) ≤ N^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  apply zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving
  refine ⟨max 2 N₀,δ,(by have := le_max_left (2 : ℝ) N₀; linarith),hδ,?_⟩
  intro N I t hNC hI hsub htlo hthi
  have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans hNC
  have hN1 : (1 : ℝ) < N := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have htp : 0 < t := (Real.rpow_pos_of_pos hNp _).trans_le htlo
  have hconst := hN₀ (N : ℝ) ((le_max_right _ _).trans hNC)
  by_cases hIempty : I = ∅
  · subst I
    simpa only [Finset.sum_empty,norm_zero] using
      Real.rpow_pos_of_pos hNp (σ-δ)
  obtain ⟨a,b,rfl⟩ := hI
  have hab : a ≤ b := Finset.nonempty_Icc.mp (Finset.nonempty_iff_ne_empty.mpr hIempty)
  have hNa : N ≤ a := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩))).1
  have hbN : b ≤ 2*N := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩))).2
  have hsum := hbound t N a b htp hN1.le (by exact_mod_cast hNa)
    (by exact_mod_cast hbN)
  have hmajor := zetaPair_power_majorant hN1.le htp hkδ ha hb htlo hthi
  have hphase : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      ∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I)) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [dirichletPhase,mul_comm Complex.I (t : ℂ)]
    rfl
  rw [hphase]
  calc
    _ ≤ B*((1+2*Real.pi)*(N : ℝ)^(σ-3*δ)) :=
      hsum.trans (mul_le_mul_of_nonneg_left hmajor (zero_le_one.trans hB))
    _ = (B*(1+2*Real.pi))*(N : ℝ)^(σ-3*δ) := by ring
    _ ≤ (N : ℝ)^δ*(N : ℝ)^(σ-3*δ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
    _ = (N : ℝ)^(σ-2*δ) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    _ < (N : ℝ)^(σ-δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)

/-- At and above height N the retained low-height condition is automatic
throughout the paper's sigma domain. -/
theorem ExponentPair.zetaLargeValueExponent_eq_bot_of_one_le_tau
    {k l σ τ : ℝ} (h : ExponentPair k l)
    (hσ : 1/2 ≤ σ) (hτ : 1 ≤ τ) (hmain : k*τ+l-k < σ) :
    zetaLargeValueExponent σ τ = ⊥ :=
  h.zetaLargeValueExponent_eq_bot (by linarith) hmain (by linarith)

/-- The classical pair suffices for the Huxley high-height nonexistence
range, without assuming any zeta-growth transfer theorem. -/
theorem zetaLargeValueExponent_eq_bot_of_classical_pair
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 1 ≤ τ) (hmain : τ/6+1/2 < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  have hpair := exponentPair_half_half.aProcess
  apply hpair.zetaLargeValueExponent_eq_bot_of_one_le_tau hσ hτ
  norm_num at *
  linarith

end TaoTrudgianYang2025
