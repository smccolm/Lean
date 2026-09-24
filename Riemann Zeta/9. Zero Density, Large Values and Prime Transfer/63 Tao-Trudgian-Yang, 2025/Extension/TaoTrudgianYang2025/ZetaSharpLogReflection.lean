import TaoTrudgianYang2025.ZetaLogReflectionTerms

/-!
# Sharp logarithmic source reflection with every error retained

The actual sharp B-process is specialized to the literal logarithmic
phase. The reflected coefficients are reciprocal weights on its true
retained stationary interval, not an assumed large-value pattern.
-/

noncomputable section
open Set Expdb Complex
open scoped FourierTransform BigOperators
namespace TaoTrudgianYang2025

theorem logarithmicSharp_source_comparison {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N T : ℝ) (a b : ℕ),
      1 ≤ N → 1 ≤ T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ‖exponentialSumAt Real.log T N a b‖ ≤
          Real.sqrt T*‖∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
            (q : ℂ)⁻¹*(q : ℂ)^(-(I*((2*Real.pi*T : ℝ) : ℂ)))‖+
          C*(N/Real.sqrt T+T^ε) := by
  obtain ⟨C,hC,hcompare⟩ := modelPhase_source_sharp_comparison
    (by norm_num : (0 : ℝ) < 1) hε
  refine ⟨C,hC,?_⟩
  intro N T a b hN hT ha hb
  have hNpos := zero_lt_one.trans_le hN
  have hTpos := zero_lt_one.trans_le hT
  have herr := hcompare N T a b hN hT ha hb Real.log 0
    (le_min (modelPhaseCurvatureLower_pos (by norm_num : (0 : ℝ) < 1)).le
      (by norm_num))
    (log_approximateModel bufferedLocalStationaryOrder (le_refl 0))
  have htri := norm_le_insert' (exponentialSumAt Real.log T N a b)
    (∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
      modelPhaseStationaryMainTerm Real.log T N q)
  rw [norm_logarithmicSharpStationarySum hTpos hNpos ha hb] at htri
  linarith

theorem dirichletInterval_sharp_log_reflection {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t : ℝ) (a b : ℕ),
      1 ≤ N → 2*Real.pi ≤ t → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ‖∑ n ∈ Finset.Icc a b, dirichletPhase n t‖ ≤
          Real.sqrt (t/(2*Real.pi))*
            ‖∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
              (q : ℂ)⁻¹*(q : ℂ)^(-(I*(t : ℂ)))‖+
          C*(N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hbound⟩ := logarithmicSharp_source_comparison hε
  refine ⟨C,hC,?_⟩
  intro N t a b hN ht ha hb
  have hpi : 0 < 2*Real.pi := by positivity
  have hT : 1 ≤ t/(2*Real.pi) := (le_div_iff₀ hpi).mpr (by simpa using ht)
  have hphase :
      ‖∑ n ∈ Finset.Icc a b, dirichletPhase n t‖ =
        ‖exponentialSumAt Real.log (t/(2*Real.pi)) N a b‖ := by
    have hh := norm_sum_cpow_neg_im_eq_logModel (zero_lt_one.trans_le hN) a b ha t
    simpa only [dirichletPhase,mul_comm I (t : ℂ)] using hh
  rw [hphase]
  have heq : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  simpa only [heq] using hbound N (t/(2*Real.pi)) a b hN hT ha hb

end TaoTrudgianYang2025
