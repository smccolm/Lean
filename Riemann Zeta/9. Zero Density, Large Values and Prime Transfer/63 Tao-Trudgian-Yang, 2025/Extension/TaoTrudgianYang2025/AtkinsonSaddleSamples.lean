import TaoTrudgianYang2025.FiniteWeightVariation

/-!
# Ordered physical samples of the two actual saddles

Positive and negative carriers produce increasing and decreasing sample
sequences respectively. Their normalized roots lie in the same fixed compact
interval throughout the already proved small-frequency source range.
-/

noncomputable section

open Complex Set

namespace TaoTrudgianYang2025

theorem atkinsonSaddleRoot_inverse_identity {A : ℝ} (hA : 0 < A) (b : ℝ) :
    atkinsonSaddleRoot A b-A/atkinsonSaddleRoot A b = b := by
  have hr := atkinsonSaddleRoot_pos hA b
  have he := atkinsonSaddleRoot_equation hA b
  field_simp
  nlinarith

theorem atkinsonSaddleRoot_monotone {A : ℝ} (hA : 0 < A) :
    Monotone (atkinsonSaddleRoot A) := by
  intro b c hbc
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hdiv := div_le_div_of_nonneg_left hA.le (atkinsonSaddleRoot_pos hA c) hlt.le
  have hb := atkinsonSaddleRoot_inverse_identity hA b
  have hc := atkinsonSaddleRoot_inverse_identity hA c
  linarith

theorem zetaAtkinsonSaddle_monotone {T : ℝ} (hT : 0 < T) :
    Monotone (zetaAtkinsonSaddle T) := by
  intro b c hbc
  exact pow_le_pow_left₀ (atkinsonSaddleRoot_pos (by positivity) b).le
    (atkinsonSaddleRoot_monotone (by positivity) hbc) 2

def atkinsonPositiveRootSample (T : ℝ) (m i : ℕ) : ℝ :=
  atkinsonSaddleRoot (T/(2*Real.pi)) (Real.sqrt ((m+i:ℕ):ℝ)) / Real.sqrt T

def atkinsonNegativeRootSample (T : ℝ) (m i : ℕ) : ℝ :=
  atkinsonSaddleRoot (T/(2*Real.pi)) (-Real.sqrt ((m+i:ℕ):ℝ)) / Real.sqrt T

theorem atkinsonPositiveRootSample_monotone {T : ℝ} (hT : 0 < T) (m : ℕ) :
    Monotone (atkinsonPositiveRootSample T m) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg T)
  apply atkinsonSaddleRoot_monotone (by positivity)
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)

theorem atkinsonNegativeRootSample_antitone {T : ℝ} (hT : 0 < T) (m : ℕ) :
    Antitone (atkinsonNegativeRootSample T m) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg T)
  apply atkinsonSaddleRoot_monotone (by positivity)
  apply neg_le_neg
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)

theorem atkinsonRootSample_mem {T : ℝ} (hT : 0 < T) (m N : ℕ)
    (hN : 10000*((m+N:ℕ):ℝ) ≤ T) (i : ℕ) (hi : i ≤ N) :
    atkinsonPositiveRootSample T m i ∈ Icc (1/4) 1 ∧
      atkinsonNegativeRootSample T m i ∈ Icc (1/4) 1 := by
  have hn : 10000*((m+i:ℕ):ℝ) ≤ T := by
    have hcast : ((m+i:ℕ):ℝ) ≤ (m+N:ℕ) := by exact_mod_cast Nat.add_le_add_left hi m
    linarith
  have hb := sqrt_nat_small_frequency hT (m+i) hn
  have hp := atkinsonSaddleRoot_small_frequency hT hb
  have hm := atkinsonSaddleRoot_small_frequency hT (b := -Real.sqrt ((m+i:ℕ):ℝ))
    (by simpa only [abs_neg] using hb)
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  constructor
  · constructor
    · apply (le_div_iff₀ hs).2
      linarith [hp.1]
    · apply (div_le_iff₀ hs).2
      linarith [hp.2]
  · constructor
    · apply (le_div_iff₀ hs).2
      linarith [hm.1]
    · apply (div_le_iff₀ hs).2
      linarith [hm.2]

theorem zetaMainMellinProfile_saddle_eq_root {T : ℝ} (hT : 0 < T) (b : ℝ) :
    zetaMainMellinProfile (zetaAtkinsonSaddle T b/T) =
      atkinsonPowerProfile 0 ((atkinsonSaddleRoot (T/(2*Real.pi)) b/Real.sqrt T)^2) := by
  unfold atkinsonPowerProfile zetaAtkinsonSaddle
  rw [div_pow,Real.sq_sqrt hT.le]
  simp only [neg_zero,Real.rpow_zero,Complex.ofReal_one,one_mul]

theorem exists_finiteVariationBound_saddleMellin :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ m N : ℕ,
      10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => zetaMainMellinProfile
        (zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))/T)) N C ∧
      FiniteVariationBound (fun i => zetaMainMellinProfile
        (zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))/T)) N C := by
  obtain ⟨C,hC,hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile 0
  refine ⟨C,hC,?_⟩
  intro T hT m N hN
  have hbound (u : ℕ → ℝ) (hm : MonotoneOn u (Iic N) ∨ AntitoneOn u (Iic N))
      (hr : ∀ i ≤ N, u i ∈ Icc (1/4) 1) :
      FiniteVariationBound (fun i => atkinsonPowerProfile 0 ((u i)^2)) N C := by
    apply finiteVariationBound_comp_of_lipschitz hC.le (by norm_num) hm hr hprofile.norm_le
    intro x hx y hy
    simpa only [mul_one] using hprofile.norm_sub_le hx hy
  constructor
  · apply (hbound _ (Or.inl ((atkinsonPositiveRootSample_monotone hT m).monotoneOn (Iic N)))
      (fun i hi => (atkinsonRootSample_mem hT m N hN i hi).1)).congr
    intro i _
    exact zetaMainMellinProfile_saddle_eq_root hT _
  · apply (hbound _ (Or.inr ((atkinsonNegativeRootSample_antitone hT m).antitoneOn (Iic N)))
      (fun i hi => (atkinsonRootSample_mem hT m N hN i hi).2)).congr
    intro i _
    exact zetaMainMellinProfile_saddle_eq_root hT _

end TaoTrudgianYang2025
