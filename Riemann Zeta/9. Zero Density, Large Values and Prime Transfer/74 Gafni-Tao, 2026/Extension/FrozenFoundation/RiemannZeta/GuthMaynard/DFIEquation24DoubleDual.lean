import RiemannZeta.GuthMaynard.DFIEquation24

/-!
# DFI equation (24): absolutely convergent double-dual reassembly

This module justifies the two Dirichlet-series interchanges in the four
double-dual branches of DFI equation (24).  It starts from the actual
Estermann weights and the actual two-variable Mellin transform.
-/

open Complex Set MeasureTheory
open scoped BigOperators ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

/-- The archimedean multiplier belonging to one DFI dual branch. -/
noncomputable def dfiDualBranchMultiplier (q : ℕ) [NeZero q] :
    DFIVoronoiDualBranch → ℂ → ℂ
  | .minusTerm => dfiVoronoiMinusMultiplier q
  | .plusTerm => dfiVoronoiPlusMultiplier q

/-- The periodic divisor coefficient used by one DFI dual branch before
the inverse additive character is separated. -/
noncomputable def dfiDualBranchCoefficientCharacter
    (q : ℕ) [NeZero q] (d : ZMod q) :
    DFIVoronoiDualBranch → ZMod q → ℂ
  | .minusTerm => dfiVoronoiCharacter q (-d⁻¹)
  | .plusTerm => dfiVoronoiCharacter q d⁻¹

theorem dfiDualBranchVerticalWeight_eq
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) (u : ℝ) :
    dfiDualBranchVerticalWeight q d branch u =
      periodicEstermann q
          (dfiDualBranchCoefficientCharacter q d branch)
          ((3 / 2 : ℂ) - (u : ℂ) * I) *
        dfiDualBranchMultiplier q branch
          (-(1 / 2 : ℂ) + (u : ℂ) * I) := by
  cases branch <;> rfl

/-- The branch-dependent periodic divisor coefficient is the ordinary
divisor weight times the inverse additive character with the branch sign. -/
theorem periodicDivisorCoeff_dfiDualBranchCoefficientCharacter
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) (n : ℕ) :
    periodicDivisorCoeff q
        (dfiDualBranchCoefficientCharacter q d branch) n =
      divisorWeight n *
        ZMod.stdAddChar (dfiSignedFrequency branch.xSign
          (d⁻¹ * (n : ZMod q))) := by
  cases branch
  · rw [show dfiDualBranchCoefficientCharacter q d .minusTerm =
        dfiVoronoiCharacter q (-d⁻¹) by rfl,
      periodicDivisorCoeff_voronoiCharacter]
    congr 2
    simp [DFIVoronoiDualBranch.xSign, dfiSignedFrequency]
  · rw [show dfiDualBranchCoefficientCharacter q d .plusTerm =
        dfiVoronoiCharacter q d⁻¹ by rfl,
      periodicDivisorCoeff_voronoiCharacter]
    rfl

/-- The residue-independent `(m,n)` Mellin integrand underlying all four
double-dual branches of DFI equation (24). -/
noncomputable def dfiEquation24DoubleDualAmplitudeIntegrand
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (divisorWeight m *
      (m : ℂ) ^ (-(1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)))) *
    (divisorWeight n *
      (n : ℂ) ^ (-(1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))) *
    (dfiDualBranchMultiplier qx xBranch
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
      dfiDualBranchMultiplier qy yBranch
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
      dfiBiMellin E
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I))

/-- The normalized, residue-independent two-frequency amplitude in DFI
equation (24). -/
noncomputable def dfiEquation24DoubleDualMellinAmplitude
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) : ℂ :=
  (((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2) *
    ∫ p : ℝ × ℝ, dfiEquation24DoubleDualAmplitudeIntegrand
      qx xBranch qy yBranch E m n p

theorem continuous_dfiDualBranchMultiplier_leftLine
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    Continuous (fun u : ℝ ↦ dfiDualBranchMultiplier q branch
      (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  cases branch
  · exact continuous_dfiVoronoiMinusMultiplier_leftLine q
  · exact continuous_dfiVoronoiPlusMultiplier_leftLine q

theorem norm_dfiDualBranchMultiplier_le
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (u : ℝ) :
    ‖dfiDualBranchMultiplier q branch
        (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2 := by
  cases branch
  · exact norm_dfiVoronoiMinusMultiplier_le q u
  · exact norm_dfiVoronoiPlusMultiplier_le q u

/-- The bare pair of archimedean Voronoi multipliers times the double
Mellin transform is absolutely integrable. -/
theorem integrable_dfiDualBranchMultipliers_mul_biMellin
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) :
    Integrable (fun p : ℝ × ℝ ↦
      dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) := by
  let Cx : ℝ := 32 * qx * dfiArchimedeanScale qx ^ 2
  let Cy : ℝ := 32 * qy * dfiArchimedeanScale qy ^ 2
  have hBase := integrable_biMellin_quadratic_weight
    hE hA hAB hC hCD hSupport (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ))
  have hMajor : Integrable (fun p : ℝ × ℝ ↦
      (Cx * Cy) * ((1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
        ‖dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using hBase.const_mul (Cx * Cy)
  have hCont : Continuous (fun p : ℝ × ℝ ↦
      dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) := by
    have hBiCont : Continuous (fun p : ℝ × ℝ ↦
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one] using
        continuous_dfiBiMellin_vertical hE hA hAB hC hCD hSupport
          (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ))
    exact (((continuous_dfiDualBranchMultiplier_leftLine qx xBranch).comp
      continuous_fst).mul
        ((continuous_dfiDualBranchMultiplier_leftLine qy yBranch).comp
          continuous_snd)).mul hBiCont
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with p
  rw [norm_mul, norm_mul]
  have hWeights :
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)‖ *
        ‖dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ ≤
      (Cx * Cy) * ((1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2) := by
    calc
      _ ≤ (Cx * (1 + |p.1|) ^ 2) *
          (Cy * (1 + |p.2|) ^ 2) :=
        mul_le_mul (norm_dfiDualBranchMultiplier_le qx xBranch p.1)
          (norm_dfiDualBranchMultiplier_le qy yBranch p.2)
          (norm_nonneg _) (by dsimp [Cx]; positivity)
      _ = _ := by ring
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hWeights
    (norm_nonneg (dfiBiMellin E
      (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
      (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))

/-- The `(m,n)` Dirichlet-series summand of the double-dual vertical
integral in DFI equation (24). -/
noncomputable def dfiEquation24DoubleMellinTerm
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) (p : ℝ × ℝ) : ℂ :=
  LSeries.term (periodicDivisorCoeff qx Φx)
      (1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)) m *
    LSeries.term (periodicDivisorCoeff qy Φy)
      (1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) n *
    (dfiDualBranchMultiplier qx xBranch
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
      dfiDualBranchMultiplier qy yBranch
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
      dfiBiMellin E
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I))

/-- Exact extraction of both inverse additive characters from one
double-series term. -/
theorem dfiEquation24DoubleMellinTerm_eq_characters_mul_amplitude
    (qx : ℕ) [NeZero qx] (dx : ZMod qx)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (dy : ZMod qy)
    (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) (p : ℝ × ℝ) :
    dfiEquation24DoubleMellinTerm
        qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
        qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
        E m n p =
      ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
          (dx⁻¹ * (m : ZMod qx))) *
        ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
          (dy⁻¹ * (n : ZMod qy))) *
        dfiEquation24DoubleDualAmplitudeIntegrand
          qx xBranch qy yBranch E m n p := by
  unfold dfiEquation24DoubleMellinTerm
    dfiEquation24DoubleDualAmplitudeIntegrand
  rw [LSeries.term_def₀ (by simp [periodicDivisorCoeff]),
    LSeries.term_def₀ (by simp [periodicDivisorCoeff]),
    periodicDivisorCoeff_dfiDualBranchCoefficientCharacter,
    periodicDivisorCoeff_dfiDualBranchCoefficientCharacter]
  ring

/-- With the constant periodic function, the double Mellin term is exactly
the residue-independent amplitude integrand. -/
theorem dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) (p : ℝ × ℝ) :
    dfiEquation24DoubleMellinTerm
        qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch E m n p =
      dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p := by
  unfold dfiEquation24DoubleMellinTerm
    dfiEquation24DoubleDualAmplitudeIntegrand
  rw [LSeries.term_def₀ (by simp [periodicDivisorCoeff]),
    LSeries.term_def₀ (by simp [periodicDivisorCoeff])]
  simp only [periodicDivisorCoeff, divisorWeight, mul_one]

theorem continuous_LSeriesTerm_threeHalfLine
    {a : ℕ → ℂ} (n : ℕ) :
    Continuous (fun u : ℝ ↦ LSeries.term a
      (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) n) := by
  by_cases hn : n = 0
  · subst n
    simpa [LSeries.term_zero] using
      (continuous_const : Continuous (fun _u : ℝ ↦ (0 : ℂ)))
  simp_rw [LSeries.term_of_ne_zero hn]
  have hExponent : Continuous (fun u : ℝ ↦
      1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by fun_prop
  have hPow : Continuous (fun u : ℝ ↦
      (n : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I))) :=
    hExponent.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
  exact continuous_const.div hPow (fun _ ↦
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))

theorem norm_LSeriesTerm_threeHalfLine
    {a : ℕ → ℂ} (n : ℕ) (u : ℝ) :
    ‖LSeries.term a
        (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) n‖ =
      ‖LSeries.term a (3 / 2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  norm_num

/-- Every fixed double Dirichlet-series summand is absolutely integrable
on the pair of reflected contours. -/
theorem integrable_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    Integrable (dfiEquation24DoubleMellinTerm
      qx Φx xBranch qy Φy yBranch E m n) := by
  let Bx : ℝ := ‖LSeries.term
    (periodicDivisorCoeff qx Φx) (3 / 2 : ℂ) m‖
  let By : ℝ := ‖LSeries.term
    (periodicDivisorCoeff qy Φy) (3 / 2 : ℂ) n‖
  have hBase := integrable_dfiDualBranchMultipliers_mul_biMellin
    hE hA hAB hC hCD hSupport qx qy xBranch yBranch
  apply hBase.bdd_mul (c := Bx * By)
  · have hx : Continuous (fun p : ℝ × ℝ ↦
        LSeries.term (periodicDivisorCoeff qx Φx)
          (1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)) m) :=
      (continuous_LSeriesTerm_threeHalfLine m).comp continuous_fst
    have hy : Continuous (fun p : ℝ × ℝ ↦
        LSeries.term (periodicDivisorCoeff qy Φy)
          (1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) n) :=
      (continuous_LSeriesTerm_threeHalfLine n).comp continuous_snd
    exact (hx.mul hy).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul]
    dsimp [Bx, By]
    rw [norm_LSeriesTerm_threeHalfLine,
      norm_LSeriesTerm_threeHalfLine]

/-- The norm integral of a fixed double-series term factors into its two
absolute Dirichlet coefficients and one common archimedean integral. -/
theorem integral_norm_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    (∫ p : ℝ × ℝ, ‖dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p‖) =
      ‖LSeries.term (periodicDivisorCoeff qx Φx) (3 / 2 : ℂ) m‖ *
        ‖LSeries.term (periodicDivisorCoeff qy Φy) (3 / 2 : ℂ) n‖ *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  unfold dfiEquation24DoubleMellinTerm
  repeat' rw [norm_mul]
  rw [norm_LSeriesTerm_threeHalfLine,
    norm_LSeriesTerm_threeHalfLine]

/-- For each first frequency, the norm integrals of the second-frequency
series are summable. -/
theorem summable_integral_norm_dfiEquation24DoubleMellinTerm_right
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) (m : ℕ) :
    Summable (fun n : ℕ ↦ ∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p‖) := by
  have hyCoeff : Summable (fun n : ℕ ↦
      ‖LSeries.term (periodicDivisorCoeff qy Φy)
        (3 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr
      (periodicDivisorCoeff_LSeriesSummable qy Φy (by norm_num))
  let K : ℝ := ‖LSeries.term (periodicDivisorCoeff qx Φx)
      (3 / 2 : ℂ) m‖ *
    ∫ p : ℝ × ℝ,
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖
  apply (hyCoeff.mul_left K).congr
  intro n
  rw [integral_norm_dfiEquation24DoubleMellinTerm]
  dsimp [K]
  ring

/-- The iterated family of norm integrals is summable in the source order
`m` then `n`. -/
theorem summable_tsum_integral_norm_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) :
    Summable (fun m : ℕ ↦ ∑' n : ℕ, ∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p‖) := by
  have hxCoeff : Summable (fun m : ℕ ↦
      ‖LSeries.term (periodicDivisorCoeff qx Φx)
        (3 / 2 : ℂ) m‖) :=
    summable_norm_iff.mpr
      (periodicDivisorCoeff_LSeriesSummable qx Φx (by norm_num))
  have hyCoeff : Summable (fun n : ℕ ↦
      ‖LSeries.term (periodicDivisorCoeff qy Φy)
        (3 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr
      (periodicDivisorCoeff_LSeriesSummable qy Φy (by norm_num))
  let Sy : ℝ := ∑' n : ℕ,
    ‖LSeries.term (periodicDivisorCoeff qy Φy) (3 / 2 : ℂ) n‖
  let J : ℝ := ∫ p : ℝ × ℝ,
    ‖dfiDualBranchMultiplier qx xBranch
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
      dfiDualBranchMultiplier qy yBranch
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
      dfiBiMellin E
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖
  have hInner (m : ℕ) :
      (∑' n : ℕ, ∫ p : ℝ × ℝ,
        ‖dfiEquation24DoubleMellinTerm
          qx Φx xBranch qy Φy yBranch E m n p‖) =
        ‖LSeries.term (periodicDivisorCoeff qx Φx)
            (3 / 2 : ℂ) m‖ * Sy * J := by
    simp_rw [integral_norm_dfiEquation24DoubleMellinTerm]
    rw [show (fun n : ℕ ↦
        ‖LSeries.term (periodicDivisorCoeff qx Φx) (3 / 2 : ℂ) m‖ *
          ‖LSeries.term (periodicDivisorCoeff qy Φy) (3 / 2 : ℂ) n‖ * J) =
      fun n : ℕ ↦
        ‖LSeries.term (periodicDivisorCoeff qx Φx) (3 / 2 : ℂ) m‖ *
          (‖LSeries.term (periodicDivisorCoeff qy Φy) (3 / 2 : ℂ) n‖ * J) by
        funext n
        ring]
    rw [tsum_mul_left, tsum_mul_right]
    dsimp [Sy]
    ring
  apply (hxCoeff.mul_right (Sy * J)).congr
  intro m
  rw [hInner m]
  ring

/-- One Mellin amplitude is bounded by the normalized `L¹` mass of its
residue-independent integrand. -/
theorem norm_dfiEquation24DoubleDualMellinAmplitude_le
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) :
    ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖ ≤
      ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
        ∫ p : ℝ × ℝ,
          ‖dfiEquation24DoubleDualAmplitudeIntegrand
            qx xBranch qy yBranch E m n p‖ := by
  unfold dfiEquation24DoubleDualMellinAmplitude
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (fun p : ℝ × ℝ ↦ dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p)) (norm_nonneg _)

/-- For fixed first frequency, the norms of the normalized DFI amplitudes
are summable in the second frequency. -/
theorem summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch) (m : ℕ) :
    Summable (fun n : ℕ ↦
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) := by
  let K : ℝ := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖
  have hBase := summable_integral_norm_dfiEquation24DoubleMellinTerm_right
    (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m
  have hBase' : Summable (fun n : ℕ ↦ ∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p‖) := by
    simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand]
      using hBase
  apply (hBase'.mul_left K).of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    exact norm_dfiEquation24DoubleDualMellinAmplitude_le
      qx xBranch qy yBranch E m n

/-- The iterated absolute masses of all normalized DFI double-dual
amplitudes are summable in source order. -/
theorem summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch) :
    Summable (fun m : ℕ ↦ ∑' n : ℕ,
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) := by
  let K : ℝ := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖
  have hBase :=
    summable_tsum_integral_norm_dfiEquation24DoubleMellinTerm
      (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch
  have hBase' : Summable (fun m : ℕ ↦ ∑' n : ℕ,
      ∫ p : ℝ × ℝ,
        ‖dfiEquation24DoubleDualAmplitudeIntegrand
          qx xBranch qy yBranch E m n p‖) := by
    simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand]
      using hBase
  apply (hBase'.mul_left K).of_nonneg_of_le
  · intro m
    exact tsum_nonneg fun _ ↦ norm_nonneg _
  · intro m
    have hAmp :=
      summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
        (E := E) qx xBranch qy yBranch m
    have hInt : Summable (fun n : ℕ ↦
        ∫ p : ℝ × ℝ,
          ‖dfiEquation24DoubleDualAmplitudeIntegrand
            qx xBranch qy yBranch E m n p‖) := by
      simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand]
        using summable_integral_norm_dfiEquation24DoubleMellinTerm_right
          (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m
    have hScaled := hInt.mul_left K
    calc
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
          ∑' n : ℕ, K * ∫ p : ℝ × ℝ,
            ‖dfiEquation24DoubleDualAmplitudeIntegrand
              qx xBranch qy yBranch E m n p‖ :=
        hAmp.tsum_le_tsum
          (fun n ↦ norm_dfiEquation24DoubleDualMellinAmplitude_le
            qx xBranch qy yBranch E m n) hScaled
      _ = K * ∑' n : ℕ, ∫ p : ℝ × ℝ,
          ‖dfiEquation24DoubleDualAmplitudeIntegrand
            qx xBranch qy yBranch E m n p‖ := by
        rw [tsum_mul_left]

/-- Multiplying both frequency variables by unit-bounded characters
preserves the source-ordered summability of the DFI amplitudes. -/
theorem summable_character_tsum_character_dfiAmplitude
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (χx χy : ℕ → ℂ)
    (hχx : ∀ m, ‖χx m‖ ≤ 1) (hχy : ∀ n, ‖χy n‖ ≤ 1) :
    Summable (fun m : ℕ ↦ χx m * ∑' n : ℕ,
      χy n * dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n) := by
  have hOuter := summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    (E := E) qx xBranch qy yBranch
  apply Summable.of_norm_bounded hOuter
  intro m
  have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
    (E := E) qx xBranch qy yBranch m
  have hInner : Summable (fun n : ℕ ↦
      χy n * dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n) := by
    apply Summable.of_norm_bounded hAmp
    intro n
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχy n)
  rw [norm_mul]
  calc
    ‖χx m‖ * ‖∑' n : ℕ,
        χy n * dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        1 * ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖ := by
      apply mul_le_mul (hχx m)
      · exact (norm_tsum_le_tsum_norm hInner.norm).trans <|
          hInner.norm.tsum_le_tsum
            (fun n ↦ by
              rw [norm_mul]
              exact mul_le_of_le_one_left (norm_nonneg _) (hχy n)) hAmp
      · exact norm_nonneg _
      · norm_num
    _ = _ := one_mul _

set_option maxHeartbeats 800000 in
/-- Absolute summability of the integrals implies almost-everywhere
pointwise summability of the norm series. -/
theorem ae_summable_norm_of_summable_integral_norm_dfi24
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, Integrable (F n) μ)
    (hFsum : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun n ↦ ‖F n x‖) := by
  have hMeas (n : ℕ) : AEMeasurable (fun x ↦ ‖F n x‖ₑ) μ :=
    (hFint n).aestronglyMeasurable.enorm
  have hEach (n : ℕ) : ∫⁻ x, ‖F n x‖ₑ ∂μ =
      ‖∫ x, ‖F n x‖ ∂μ‖₊ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hFint n).norm,
      ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x ↦ norm_nonneg (F n x))]
    simp only [coe_nnnorm]
  have hFinite : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ ≠ ⊤ := by
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  rw [← lintegral_tsum hMeas] at hFinite
  refine (ae_lt_top' (AEMeasurable.tsum hMeas) hFinite).mono ?_
  intro x hx
  change Summable (fun n ↦ (‖F n x‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact hx.ne

set_option maxHeartbeats 800000 in
/-- The `L¹` norm of an absolutely integrable series is bounded by the sum
of the `L¹` norms of its terms. -/
theorem integral_norm_tsum_le_tsum_integral_norm_dfi24
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, Integrable (F n) μ)
    (hFsum : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂μ)) :
    (∫ x, ‖∑' n, F n x‖ ∂μ) ≤
      ∑' n, ∫ x, ‖F n x‖ ∂μ := by
  have hSeriesInt := integrable_tsum_of_summable_integral_norm_dfi
    hFint hFsum
  have hNormTermInt (n : ℕ) : Integrable (fun x ↦ ‖F n x‖) μ :=
    (hFint n).norm
  have hNormSum : Summable (fun n ↦
      ∫ x, ‖(‖F n x‖ : ℝ)‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_norm] using hFsum
  have hPointwise := ae_summable_norm_of_summable_integral_norm_dfi24
    hFint hFsum
  have hNormMeas (n : ℕ) :
      AEMeasurable (fun x ↦ ‖F n x‖ₑ) μ :=
    (hFint n).aestronglyMeasurable.enorm
  have hEach (n : ℕ) :
      ∫⁻ x, ‖F n x‖ₑ ∂μ =
        ‖∫ x, ‖F n x‖ ∂μ‖₊ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hFint n).norm,
      ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x ↦ norm_nonneg (F n x))]
    simp only [coe_nnnorm]
  have hFiniteSum : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ ≠ ⊤ := by
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  have hNormSeriesInt : Integrable (fun x ↦ ∑' n, ‖F n x‖) μ := by
    refine ⟨AEStronglyMeasurable.tsum
      (fun n ↦ (hNormTermInt n).aestronglyMeasurable), ?_⟩
    dsimp [HasFiniteIntegral]
    have hFinite : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ < ⊤ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hFiniteSum
    convert hFinite using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum,
      enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  calc
    (∫ x, ‖∑' n, F n x‖ ∂μ) ≤
        ∫ x, ∑' n, ‖F n x‖ ∂μ := by
      apply integral_mono_ae hSeriesInt.norm hNormSeriesInt
      filter_upwards [hPointwise] with x hx
      exact norm_tsum_le_tsum_norm hx
    _ = ∑' n, ∫ x, ‖F n x‖ ∂μ := by
      rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
        hNormTermInt hNormSum]

/-- For a fixed first Dirichlet frequency, the second-frequency series
is integrable on the pair of reflected contours. -/
theorem integrable_tsum_dfiEquation24DoubleMellinTerm_right
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) (m : ℕ) :
    Integrable (fun p : ℝ × ℝ ↦ ∑' n : ℕ,
      dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p) := by
  apply integrable_tsum_of_summable_integral_norm_dfi
  · intro n
    exact integrable_dfiEquation24DoubleMellinTerm
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch m n
  · exact summable_integral_norm_dfiEquation24DoubleMellinTerm_right
      qx Φx xBranch qy Φy yBranch m

/-- The outer series of `L¹` norms of the already-summed inner series is
summable.  This is the second Tonelli estimate needed for equation (24). -/
theorem summable_integral_norm_tsum_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) :
    Summable (fun m : ℕ ↦ ∫ p : ℝ × ℝ,
      ‖∑' n : ℕ, dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p‖) := by
  have hMajor :=
    summable_tsum_integral_norm_dfiEquation24DoubleMellinTerm
      (E := E) qx Φx xBranch qy Φy yBranch
  apply hMajor.of_nonneg_of_le
  · intro m
    exact integral_nonneg fun _ ↦ norm_nonneg _
  · intro m
    exact integral_norm_tsum_le_tsum_integral_norm_dfi24
      (fun n ↦ integrable_dfiEquation24DoubleMellinTerm
        hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch m n)
      (summable_integral_norm_dfiEquation24DoubleMellinTerm_right
        qx Φx xBranch qy Φy yBranch m)

/-- Both absolutely convergent Dirichlet series may be moved through the
two-variable vertical integral, in the same `m`-then-`n` order used by
DFI equation (24). -/
theorem integral_tsum_tsum_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) :
    (∫ p : ℝ × ℝ, ∑' m : ℕ, ∑' n : ℕ,
      dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p) =
      ∑' m : ℕ, ∑' n : ℕ, ∫ p : ℝ × ℝ,
        dfiEquation24DoubleMellinTerm
          qx Φx xBranch qy Φy yBranch E m n p := by
  have hInnerInt (m : ℕ) :=
    integrable_tsum_dfiEquation24DoubleMellinTerm_right
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch m
  have hOuterSum :=
    summable_integral_norm_tsum_dfiEquation24DoubleMellinTerm
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    hInnerInt hOuterSum]
  congr 1
  funext m
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n ↦ integrable_dfiEquation24DoubleMellinTerm
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch m n)
    (summable_integral_norm_dfiEquation24DoubleMellinTerm_right
      qx Φx xBranch qy Φy yBranch m)]

/-- Pointwise expansion of the two actual Estermann factors on the
reflected contours into the source-ordered pair of Dirichlet series. -/
theorem dfiDualBranchWeights_mul_biMellin_eq_tsum_tsum
    (qx : ℕ) [NeZero qx] (dx : ZMod qx)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (dy : ZMod qy)
    (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (p : ℝ × ℝ) :
    dfiDualBranchVerticalWeight qx dx xBranch p.1 *
        dfiDualBranchVerticalWeight qy dy yBranch p.2 *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) =
      ∑' m : ℕ, ∑' n : ℕ,
        dfiEquation24DoubleMellinTerm
          qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
          qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
          E m n p := by
  rw [dfiDualBranchVerticalWeight_eq,
    dfiDualBranchVerticalWeight_eq]
  rw [periodicEstermann_eq_LSeries qx
      (dfiDualBranchCoefficientCharacter qx dx xBranch) (by norm_num),
    periodicEstermann_eq_LSeries qy
      (dfiDualBranchCoefficientCharacter qy dy yBranch) (by norm_num)]
  unfold LSeries
  symm
  calc
    (∑' m : ℕ, ∑' n : ℕ,
        dfiEquation24DoubleMellinTerm
          qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
          qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
          E m n p) =
        ∑' m : ℕ,
          LSeries.term (periodicDivisorCoeff qx
              (dfiDualBranchCoefficientCharacter qx dx xBranch))
              (1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)) m *
            ((∑' n : ℕ,
              LSeries.term (periodicDivisorCoeff qy
                (dfiDualBranchCoefficientCharacter qy dy yBranch))
                (1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) n) *
              (dfiDualBranchMultiplier qx xBranch
                  (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
                dfiDualBranchMultiplier qy yBranch
                  (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
                dfiBiMellin E
                  (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
                  (-(1 / 2 : ℂ) + (p.2 : ℂ) * I))) := by
      apply tsum_congr
      intro m
      unfold dfiEquation24DoubleMellinTerm
      rw [show (fun n : ℕ ↦
          LSeries.term (periodicDivisorCoeff qx
              (dfiDualBranchCoefficientCharacter qx dx xBranch))
              (1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)) m *
            LSeries.term (periodicDivisorCoeff qy
              (dfiDualBranchCoefficientCharacter qy dy yBranch))
              (1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) n *
            (dfiDualBranchMultiplier qx xBranch
                (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
              dfiDualBranchMultiplier qy yBranch
                (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
              dfiBiMellin E
                (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
                (-(1 / 2 : ℂ) + (p.2 : ℂ) * I))) =
          fun n : ℕ ↦
            LSeries.term (periodicDivisorCoeff qx
                (dfiDualBranchCoefficientCharacter qx dx xBranch))
                (1 - (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)) m *
              (LSeries.term (periodicDivisorCoeff qy
                  (dfiDualBranchCoefficientCharacter qy dy yBranch))
                  (1 - (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) n *
                (dfiDualBranchMultiplier qx xBranch
                    (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
                  dfiDualBranchMultiplier qy yBranch
                    (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
                  dfiBiMellin E
                    (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
                    (-(1 / 2 : ℂ) + (p.2 : ℂ) * I))) by
            funext n
            ring_nf]
      rw [tsum_mul_left, tsum_mul_right]
    _ = _ := by
      rw [tsum_mul_right]
      ring_nf

/-- The full source-ordered double Dirichlet series is integrable on the
pair of reflected contours. -/
theorem integrable_tsum_tsum_dfiEquation24DoubleMellinTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (Φx : ZMod qx → ℂ)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (Φy : ZMod qy → ℂ)
    (yBranch : DFIVoronoiDualBranch) :
    Integrable (fun p : ℝ × ℝ ↦ ∑' m : ℕ, ∑' n : ℕ,
      dfiEquation24DoubleMellinTerm
        qx Φx xBranch qy Φy yBranch E m n p) := by
  apply integrable_tsum_of_summable_integral_norm_dfi
  · intro m
    exact integrable_tsum_dfiEquation24DoubleMellinTerm_right
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch m
  · exact summable_integral_norm_tsum_dfiEquation24DoubleMellinTerm
      hE hA hAB hC hCD hSupport qx Φx xBranch qy Φy yBranch

/-- Exact absolutely convergent expansion of the iterated two-variable
vertical integral in DFI equation (24). -/
theorem integral_integral_dfiDualBranchWeights_eq_tsum_tsum
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx : ℕ) [NeZero qx] (dx : ZMod qx)
    (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (dy : ZMod qy)
    (yBranch : DFIVoronoiDualBranch) :
    (∫ u : ℝ, ∫ v : ℝ,
      dfiDualBranchVerticalWeight qx dx xBranch u *
        dfiDualBranchVerticalWeight qy dy yBranch v *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (u : ℂ) * I)
            (-(1 / 2 : ℂ) + (v : ℂ) * I)) =
      ∑' m : ℕ, ∑' n : ℕ, ∫ p : ℝ × ℝ,
        dfiEquation24DoubleMellinTerm
          qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
          qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
          E m n p := by
  let F : ℝ × ℝ → ℂ := fun p ↦ ∑' m : ℕ, ∑' n : ℕ,
    dfiEquation24DoubleMellinTerm
      qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
      qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
      E m n p
  let W : ℝ × ℝ → ℂ := fun p ↦
    dfiDualBranchVerticalWeight qx dx xBranch p.1 *
      dfiDualBranchVerticalWeight qy dy yBranch p.2 *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)
  have hFint : Integrable F := by
    simpa [F] using
      integrable_tsum_tsum_dfiEquation24DoubleMellinTerm
        hE hA hAB hC hCD hSupport
        qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
        qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
  have hWF : ∀ p, W p = F p := by
    intro p
    exact dfiDualBranchWeights_mul_biMellin_eq_tsum_tsum
      qx dx xBranch qy dy yBranch E p
  have hWint : Integrable W :=
    hFint.congr (Filter.Eventually.of_forall fun p ↦ (hWF p).symm)
  calc
    (∫ u : ℝ, ∫ v : ℝ,
        dfiDualBranchVerticalWeight qx dx xBranch u *
          dfiDualBranchVerticalWeight qy dy yBranch v *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (u : ℂ) * I)
              (-(1 / 2 : ℂ) + (v : ℂ) * I)) =
        ∫ p : ℝ × ℝ, W p := by
      rw [Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.integral_prod W hWint]
    _ = ∫ p : ℝ × ℝ, F p := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hWF
    _ = _ := by
      simpa [F] using
        integral_tsum_tsum_dfiEquation24DoubleMellinTerm
          hE hA hAB hC hCD hSupport
          qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
          qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch

/-- Each actual double-dual Voronoi branch is the normalized,
source-ordered double series of its two-frequency Mellin amplitudes. -/
theorem dfiVoronoiDualBranch_dualBranch_eq_tsum_tsum_integrals
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (dx : ZMod qx) (dy : ZMod qy)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    dfiVoronoiBranchValue qx dx xBranch.toBranch
        (fun x ↦ dfiVoronoiBranchValue qy dy yBranch.toBranch (E x)) =
      (((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2) *
        ∑' m : ℕ, ∑' n : ℕ, ∫ p : ℝ × ℝ,
          dfiEquation24DoubleMellinTerm
            qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
            qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
            E m n p := by
  rw [dfiVoronoiDualBranch_dualBranch_eq_doubleVertical
    hE hA hAB hC hCD hSupport qx qy dx dy xBranch yBranch]
  rw [integral_integral_dfiDualBranchWeights_eq_tsum_tsum
    hE hA hAB hC hCD hSupport qx dx xBranch qy dy yBranch]

/-- Source-facing double-dual branch formula: both inverse additive
characters are explicit and the remaining amplitude is independent of the
primitive residue. -/
theorem dfiVoronoiDualBranch_dualBranch_eq_character_amplitudes
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (dx : ZMod qx) (dy : ZMod qy)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    dfiVoronoiBranchValue qx dx xBranch.toBranch
        (fun x ↦ dfiVoronoiBranchValue qy dy yBranch.toBranch (E x)) =
      ∑' m : ℕ, ∑' n : ℕ,
        ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            (dx⁻¹ * (m : ZMod qx))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
            (dy⁻¹ * (n : ZMod qy))) *
          dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n := by
  rw [dfiVoronoiDualBranch_dualBranch_eq_tsum_tsum_integrals
    hE hA hAB hC hCD hSupport qx qy dx dy xBranch yBranch]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show (fun p : ℝ × ℝ ↦
      dfiEquation24DoubleMellinTerm
        qx (dfiDualBranchCoefficientCharacter qx dx xBranch) xBranch
        qy (dfiDualBranchCoefficientCharacter qy dy yBranch) yBranch
        E m n p) =
      fun p : ℝ × ℝ ↦
        (ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            (dx⁻¹ * (m : ZMod qx))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
            (dy⁻¹ * (n : ZMod qy)))) *
          dfiEquation24DoubleDualAmplitudeIntegrand
            qx xBranch qy yBranch E m n p by
      funext p
      rw [dfiEquation24DoubleMellinTerm_eq_characters_mul_amplitude],
    MeasureTheory.integral_const_mul]
  unfold dfiEquation24DoubleDualMellinAmplitude
  ring

/-- Negating the source residue reverses the branch sign exactly as in the
second physical variable of DFI equation (23). -/
theorem dfiSignedFrequency_xSign_neg_inverse_eq_ySign
    {q : ℕ} [NeZero q] (branch : DFIVoronoiDualBranch)
    (d : ZMod q) (hd : IsUnit d) (n : ℕ) :
    dfiSignedFrequency branch.xSign ((-d)⁻¹ * (n : ZMod q)) =
      dfiSignedFrequency branch.ySign (d⁻¹ * (n : ZMod q)) := by
  have hinv : (-d)⁻¹ = -(d⁻¹) :=
    ZMod.inv_eq_of_mul_eq_one q (-d) (-(d⁻¹)) (by
      rw [neg_mul_neg, ZMod.mul_inv_of_unit d hd])
  cases branch <;>
    simp only [DFIVoronoiDualBranch.xSign, DFIVoronoiDualBranch.ySign,
      dfiSignedFrequency] <;>
    rw [hinv] <;> ring

/-- The literal primitive-residue contribution of one of the four
double-dual branches in DFI equation (24). -/
noncomputable def dfiEquation24ActualDualDualContribution
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d ↦ d.Coprime q),
    ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
      dfiVoronoiBranchValue (dfiReducedModulus a q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)) xBranch.toBranch
        (fun x ↦
          dfiVoronoiBranchValue (dfiReducedModulus b q).denominator
            (-((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator))) yBranch.toBranch
            (E x))

/-- The source-facing double-dual contribution is exactly the corresponding
literal member of the nine-branch reduced equation-(24) expansion. -/
theorem dfiEquation24ReducedBranchContribution_dual_dual
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) :
    dfiEquation24ReducedBranchContribution q a b h
        xBranch.toBranch yBranch.toBranch E =
      dfiEquation24ActualDualDualContribution
        q a b h xBranch yBranch E := by
  unfold dfiEquation24ReducedBranchContribution
    dfiEquation24ActualDualDualContribution
  apply Finset.sum_congr rfl
  intro d _hd
  congr 2
  push_cast
  ring

/-- Exact DFI-(24) reassembly of a literal double-dual branch as a
source-ordered Kloosterman series.  Both infinite-sum interchanges are
justified by the preceding absolute-convergence theorems. -/
theorem dfiEquation24ActualDualDualContribution_eq_kloosterman
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    dfiEquation24ActualDualDualContribution
        q a b h xBranch yBranch E =
      dfiEquation24DualDualKloosterman q a b h
        xBranch.xSign yBranch.ySign
        (dfiEquation24DoubleDualMellinAmplitude
          (dfiReducedModulus a q).denominator xBranch
          (dfiReducedModulus b q).denominator yBranch E) := by
  let qa := (dfiReducedModulus a q).denominator
  let qb := (dfiReducedModulus b q).denominator
  let xa : ℕ → ZMod qa := fun d ↦
    (((dfiReducedModulus a q).numerator * d : ℕ) : ZMod qa)
  let yb : ℕ → ZMod qb := fun d ↦
    (((dfiReducedModulus b q).numerator * d : ℕ) : ZMod qb)
  let amp : ℕ → ℕ → ℂ :=
    dfiEquation24DoubleDualMellinAmplitude qa xBranch qb yBranch E
  let s := (Finset.range q).filter (fun d ↦ d.Coprime q)
  unfold dfiEquation24ActualDualDualContribution
  simp_rw [dfiVoronoiDualBranch_dualBranch_eq_character_amplitudes
    hE hA hAB hC hCD hSupport]
  simp_rw [← tsum_mul_left]
  change (∑ d ∈ s, ∑' m : ℕ, ∑' n : ℕ,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            ((xa d)⁻¹ * (m : ZMod qa))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
              ((-yb d)⁻¹ * (n : ZMod qb))) * amp m n)) = _
  have hOuter : ∀ d ∈ s, Summable (fun m : ℕ ↦
      ∑' n : ℕ,
        ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
          (ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
              ((xa d)⁻¹ * (m : ZMod qa))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
              ((-yb d)⁻¹ * (n : ZMod qb))) * amp m n)) := by
    intro d _hd
    simpa only [tsum_mul_left, mul_assoc] using
      summable_character_tsum_character_dfiAmplitude
        (E := E) qa xBranch qb yBranch
        (fun m ↦ ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
          ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            ((xa d)⁻¹ * (m : ZMod qa))))
        (fun n ↦ ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
          ((-yb d)⁻¹ * (n : ZMod qb))))
        (by intro m; simp) (by intro n; simp)
  rw [← Summable.tsum_finsetSum hOuter]
  apply tsum_congr
  intro m
  have hInner : ∀ d ∈ s, Summable (fun n : ℕ ↦
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            ((xa d)⁻¹ * (m : ZMod qa))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
              ((-yb d)⁻¹ * (n : ZMod qb))) * amp m n)) := by
    intro d _hd
    have hAmp :=
      summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
        (E := E) qa xBranch qb yBranch m
    have hAmp' : Summable (fun n : ℕ ↦ ‖amp m n‖) := by
      simpa only [amp] using hAmp
    apply Summable.of_norm_bounded hAmp'
    intro n
    simp
  rw [← Summable.tsum_finsetSum hInner]
  apply tsum_congr
  intro n
  have hy (d : ℕ) (hd : d ∈ s) :
      ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
          ((-yb d)⁻¹ * (n : ZMod qb))) =
        ZMod.stdAddChar (dfiSignedFrequency yBranch.ySign
          ((yb d)⁻¹ * (n : ZMod qb))) := by
    apply congrArg ZMod.stdAddChar
    exact dfiSignedFrequency_xSign_neg_inverse_eq_ySign
      yBranch (yb d)
        (by
          dsimp [yb, qb]
          exact dfiReducedModulus_frequency_isUnit b q d
            (Finset.mem_filter.mp hd).2) n
  rw [show (∑ d ∈ s,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            ((xa d)⁻¹ * (m : ZMod qa))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.xSign
              ((-yb d)⁻¹ * (n : ZMod qb))) * amp m n)) =
      (∑ d ∈ s,
        ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
          ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
            ((xa d)⁻¹ * (m : ZMod qa))) *
          ZMod.stdAddChar (dfiSignedFrequency yBranch.ySign
            ((yb d)⁻¹ * (n : ZMod qb)))) * amp m n by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hy d hd]
    ring]
  change _ = kloostermanSumZMod q (-h : ZMod q)
      (dfiSignedFrequency xBranch.xSign
          (dfiLiftedInverseFrequency a q m) +
        dfiSignedFrequency yBranch.ySign
          (dfiLiftedInverseFrequency b q n)) * amp m n
  rw [show (∑ d ∈ s,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar (dfiSignedFrequency xBranch.xSign
          ((xa d)⁻¹ * (m : ZMod qa))) *
        ZMod.stdAddChar (dfiSignedFrequency yBranch.ySign
          ((yb d)⁻¹ * (n : ZMod qb)))) =
      kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency xBranch.xSign
            (dfiLiftedInverseFrequency a q m) +
          dfiSignedFrequency yBranch.ySign
            (dfiLiftedInverseFrequency b q n)) by
    simpa [s, xa, yb, qa, qb] using
      dfiEquation24_two_reduced_inverse_coefficients_eq
        xBranch.xSign yBranch.ySign a b q m n h]

end RiemannZeta.GuthMaynard
