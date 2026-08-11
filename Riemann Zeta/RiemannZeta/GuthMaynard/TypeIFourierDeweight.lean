import RiemannZeta.GuthMaynard.TypeIReflection

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# Shared logarithmic Fourier deweighting

The main theorem is deliberately independent of the Type-I cutoff.  Any
Schwartz weight in logarithmic coordinates is removed by the same exact
Fourier-inversion identity, so the theorem applies both before reflection and
to the smooth weight on the reflected `T/N` block.
-/

/-- Exact Fourier deweighting of a finite Dirichlet block.  The output has
literal coefficient `1`; all smooth amplitude is carried by the common
Fourier transform and a common ordinate shift. -/
theorem fourierDeweightFiniteBlock_native
    (f : 𝓢(ℝ, ℂ)) (S : Finset ℕ) (t : ℝ)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, f (Real.log n) * (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∫ ξ : ℝ, 𝓕 f ξ *
        ∑ n ∈ S,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
  have hinversion (u : ℝ) :
      f u = ∫ ξ : ℝ,
        Complex.exp (((2 * Real.pi * (ξ * u) : ℝ) : ℂ) * I) * 𝓕 f ξ := by
    have hpairMap : 𝓕⁻ (𝓕 f) = f :=
      FourierTransform.fourierInv_fourier_eq f
    have hpair := congrArg (fun g : 𝓢(ℝ, ℂ) => g u) hpairMap
    change (𝓕⁻ (𝓕 f)) u = f u at hpair
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hpair
    simpa only [Real.inner_apply, smul_eq_mul] using hpair.symm
  have hintegrable (n : ℕ) (hn : 0 < n) : Integrable
      (fun ξ : ℝ => 𝓕 f ξ *
        (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
    have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hcontinuous : Continuous (fun ξ : ℝ =>
        (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
      apply Continuous.const_cpow
      · fun_prop
      · exact Or.inl hnNe
    have hfIntegrable : Integrable (fun ξ : ℝ => 𝓕 f ξ) := (𝓕 f).integrable
    apply hfIntegrable.mul_bdd (c := 1) hcontinuous.aestronglyMeasurable
    filter_upwards with ξ
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  calc
    (∑ n ∈ S, f (Real.log n) * (n : ℂ) ^ (-(t : ℂ) * I)) =
        ∑ n ∈ S, ∫ ξ : ℝ,
          𝓕 f ξ *
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPos := hS n hn
      have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
      rw [hinversion]
      rw [← MeasureTheory.integral_mul_const]
      apply integral_congr_ae
      filter_upwards with ξ
      have hphase :
          Complex.exp (((2 * Real.pi * (ξ * Real.log n) : ℝ) : ℂ) * I) *
              (n : ℂ) ^ (-(t : ℂ) * I) =
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
        rw [Complex.cpow_def_of_ne_zero hnNe, Complex.cpow_def_of_ne_zero hnNe]
        have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
        have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
          change Complex.log ((n : ℝ) : ℂ) = (Real.log (n : ℝ) : ℂ)
          exact (Complex.ofReal_log hnReal.le).symm
        rw [hlog]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        (Complex.exp (((2 * Real.pi * (ξ * Real.log n) : ℝ) : ℂ) * I) * 𝓕 f ξ) *
              (n : ℂ) ^ (-(t : ℂ) * I) =
            𝓕 f ξ *
              (Complex.exp (((2 * Real.pi * (ξ * Real.log n) : ℝ) : ℂ) * I) *
                (n : ℂ) ^ (-(t : ℂ) * I)) := by ring
        _ = 𝓕 f ξ *
              (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
            rw [hphase]
    _ = ∫ ξ : ℝ, ∑ n ∈ S,
          𝓕 f ξ *
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
      rw [integral_finsetSum]
      intro n hn
      exact hintegrable n (hS n hn)
    _ = ∫ ξ : ℝ, 𝓕 f ξ *
        ∑ n ∈ S,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]

/-- Source smooth weight in logarithmic coordinates, including the fixed
real-part factor. -/
noncomputable def typeILogWeight
    (Y A r : ℕ) (σ u : ℝ) : ℂ :=
  (typeISourceSmoothWeight Y A r (Real.exp u) : ℂ) *
    Complex.exp ((((-σ * u : ℝ) : ℂ)))

theorem contDiff_typeILogWeight
    (Y A r : ℕ) (σ : ℝ) : ContDiff ℝ ∞ (typeILogWeight Y A r σ) := by
  unfold typeILogWeight
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp u) := Real.contDiff_exp
  have hWeight : ContDiff ℝ ∞ (fun u : ℝ =>
      (typeISourceSmoothWeight Y A r (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_typeISourceSmoothWeight Y A r).comp hExp)
  have hPower : ContDiff ℝ ∞ (fun u : ℝ =>
      Complex.exp ((((-σ * u : ℝ) : ℂ)))) := by
    have hInside : ContDiff ℝ ∞ (fun u : ℝ => -σ * u) := by fun_prop
    exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp hInside)
  exact hWeight.mul hPower

theorem hasCompactSupport_typeILogWeight
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) :
    HasCompactSupport (typeILogWeight Y A r σ) := by
  let Q : ℝ := (2 ^ r * Y : ℕ)
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hhalf : 0 < Q / 2 := by positivity
  have htwo : 0 < 2 * Q := by positivity
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (Q / 2)) (Real.log (2 * Q))))
  intro u hu
  rw [Set.mem_Icc, not_and_or] at hu
  have hcut : typeIDyadicCutoff (Real.exp u / Q) = 0 := by
    rcases hu with hu | hu
    · apply typeIDyadicCutoff_eq_zero_of_le_half
      rw [div_le_iff₀ hQ]
      have hexp : Real.exp u ≤ Q / 2 := by
        rw [← Real.exp_log hhalf]
        exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
      linarith
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      rw [le_div_iff₀ hQ]
      have hexp : 2 * Q ≤ Real.exp u := by
        rw [← Real.exp_log htwo]
        exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
      exact hexp
  unfold typeILogWeight typeISourceSmoothWeight
  change ((typeITailBoundary Y A (Real.exp u) *
      typeIDyadicCutoff (Real.exp u / Q) : ℝ) : ℂ) *
        Complex.exp (((-σ * u : ℝ) : ℂ)) = 0
  rw [hcut]
  simp

/-- The logarithmic source weight as a Schwartz function. -/
noncomputable def typeILogWeightSchwartz
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeILogWeight Y A r σ hY).toSchwartzMap
    (contDiff_typeILogWeight Y A r σ)

@[simp]
theorem typeILogWeightSchwartz_apply
    (Y A r : ℕ) (σ u : ℝ) (hY : 0 < Y) :
    typeILogWeightSchwartz Y A r σ hY u =
      typeILogWeight Y A r σ u := rfl

theorem typeILogWeight_log_nat
    (Y A r n : ℕ) (σ : ℝ) (hn : 0 < n) :
    typeILogWeight Y A r σ (Real.log n) =
      typeISourceSmoothWeight Y A r n * (n : ℂ) ^ (-(σ : ℂ)) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  unfold typeILogWeight
  rw [Real.exp_log hnReal, hbase, Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    ← Complex.ofReal_log hnReal.le]
  simp only [ofReal_neg, ofReal_mul]
  ring_nf

/-- Concrete deweighting of the original source block.  This is the short
branch application of the shared theorem; the same
`fourierDeweightFiniteBlock_native` theorem applies after reflection. -/
theorem typeISourceSmoothBlock_fourierDeweight
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    typeISourceSmoothBlock Y A r σ t =
      ∫ ξ : ℝ, 𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
        ∑ n ∈ Finset.Icc 1 (A + 1),
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
  rw [typeISourceSmoothBlock]
  have hPositive : ∀ n ∈ Finset.Icc 1 (A + 1), 0 < n := by
    intro n hn
    exact Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
  rw [← fourierDeweightFiniteBlock_native
    (typeILogWeightSchwartz Y A r σ hY) (Finset.Icc 1 (A + 1)) t hPositive]
  apply Finset.sum_congr rfl
  intro n hn
  rw [typeILogWeightSchwartz_apply,
    typeILogWeight_log_nat Y A r n σ (hPositive n hn)]

/-- The phase-derived leading weight after the medium Type-I B-process,
written in logarithmic coordinates.  For Mathlib's Fourier convention the
negative mode `-m` has stationary point `t / (2πm)`.  Thus, with
`C = t / (2πQ)`, the weight is `ψ(C/eᵘ) (C/eᵘ)^(1-σ)`.

The displayed formula in ANTEDB Lemma 11.5 has `2πt/(mQ)` instead.  That
factor is incompatible with the derivative of the phase in the same display;
this definition follows the exact Poisson identity proved in
`typeIReflectionFourier_neg_eq_stationaryIntegral`. -/
noncomputable def typeIReflectedLogWeight
    (Q : ℕ) (t σ u : ℝ) : ℂ :=
  let C := t / (2 * Real.pi * Q)
  (typeIDyadicCutoff (C * Real.exp (-u)) : ℂ) *
    Complex.exp (((((1 - σ) * (Real.log C - u) : ℝ) : ℂ)))

theorem contDiff_typeIReflectedLogWeight
    (Q : ℕ) (t σ : ℝ) :
    ContDiff ℝ ∞ (typeIReflectedLogWeight Q t σ) := by
  unfold typeIReflectedLogWeight
  have hlinear : ContDiff ℝ ∞ (fun u : ℝ =>
      (1 - σ) * (Real.log (t / (2 * Real.pi * (Q : ℝ))) - u)) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_typeIDyadicCutoff.comp (by fun_prop))).mul
    (Complex.contDiff_exp.comp
      (Complex.ofRealCLM.contDiff.comp hlinear))

theorem hasCompactSupport_typeIReflectedLogWeight
    (Q : ℕ) (t σ : ℝ) (hQ : 0 < Q) (ht : 0 < t) :
    HasCompactSupport (typeIReflectedLogWeight Q t σ) := by
  let C : ℝ := t / (2 * Real.pi * Q)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hhalf : 0 < C / 2 := by positivity
  have htwo : 0 < 2 * C := by positivity
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (C / 2)) (Real.log (2 * C))))
  intro u hu
  rw [Set.mem_Icc, not_and_or] at hu
  have hcut : typeIDyadicCutoff (C * Real.exp (-u)) = 0 := by
    rcases hu with hu | hu
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      have hu' : u < Real.log (C / 2) := lt_of_not_ge hu
      have hexp : Real.exp u < C / 2 := by
        rw [← Real.exp_log hhalf]
        exact Real.exp_lt_exp.mpr hu'
      have hexpPos : 0 < Real.exp u := Real.exp_pos u
      rw [show Real.exp (-u) = (Real.exp u)⁻¹ by rw [Real.exp_neg]]
      rw [show C * (Real.exp u)⁻¹ = C / Real.exp u by ring]
      rw [le_div_iff₀ hexpPos]
      nlinarith
    · apply typeIDyadicCutoff_eq_zero_of_le_half
      have hu' : Real.log (2 * C) < u := lt_of_not_ge hu
      have hexp : 2 * C < Real.exp u := by
        rw [← Real.exp_log htwo]
        exact Real.exp_lt_exp.mpr hu'
      have hexpPos : 0 < Real.exp u := Real.exp_pos u
      rw [show Real.exp (-u) = (Real.exp u)⁻¹ by rw [Real.exp_neg]]
      rw [mul_inv_le_iff₀ hexpPos]
      nlinarith
  unfold typeIReflectedLogWeight
  change (typeIDyadicCutoff (C * Real.exp (-u)) : ℂ) *
      Complex.exp (((((1 - σ) * (Real.log C - u) : ℝ) : ℂ))) = 0
  rw [hcut]
  simp

/-- Schwartz realization of the reflected logarithmic amplitude. -/
noncomputable def typeIReflectedLogWeightSchwartz
    (Q : ℕ) (t σ : ℝ) (hQ : 0 < Q) (ht : 0 < t) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeIReflectedLogWeight Q t σ hQ ht).toSchwartzMap
    (contDiff_typeIReflectedLogWeight Q t σ)

@[simp]
theorem typeIReflectedLogWeightSchwartz_apply
    (Q : ℕ) (t σ u : ℝ) (hQ : 0 < Q) (ht : 0 < t) :
    typeIReflectedLogWeightSchwartz Q t σ hQ ht u =
      typeIReflectedLogWeight Q t σ u := rfl

/-- Literal evaluation of the reflected amplitude at a positive integer.
This records the source formula without burying a normalization in a
coefficient definition. -/
theorem typeIReflectedLogWeight_log_nat
    (Q n : ℕ) (t σ : ℝ) (hQ : 0 < Q) (ht : 0 < t) (hn : 0 < n) :
    typeIReflectedLogWeight Q t σ (Real.log n) =
      (typeIDyadicCutoff
        ((t / (2 * Real.pi * Q)) / n) : ℂ) *
        Complex.exp (((((1 - σ) *
          Real.log ((t / (2 * Real.pi * Q)) / n) : ℝ) : ℂ))) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 < t / (2 * Real.pi * (Q : ℝ)) := by positivity
  dsimp [typeIReflectedLogWeight]
  rw [Real.exp_neg, Real.exp_log hnReal]
  have hratio : (t / (2 * Real.pi * (Q : ℝ))) * ((n : ℝ)⁻¹) =
      (t / (2 * Real.pi * (Q : ℝ))) / (n : ℝ) := by ring
  rw [hratio]
  congr 2
  rw [Real.log_div hC.ne' hnReal.ne']

/-- Exact Fourier deweighting of the reflected medium block.  This is the
same theorem as for the short source block, now instantiated with the
actual reflected amplitude and therefore producing a literal coefficient-one
Dirichlet polynomial on the selected dual interval. -/
theorem typeIReflectedBlock_fourierDeweight
    (Q : ℕ) (t σ : ℝ) (S : Finset ℕ)
    (hQ : 0 < Q) (ht : 0 < t) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S,
        typeIReflectedLogWeight Q t σ (Real.log n) *
          (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∫ ξ : ℝ, 𝓕 (typeIReflectedLogWeightSchwartz Q t σ hQ ht) ξ *
        ∑ n ∈ S,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
  simpa only [typeIReflectedLogWeightSchwartz_apply] using
    fourierDeweightFiniteBlock_native
      (typeIReflectedLogWeightSchwartz Q t σ hQ ht) S t hS

end RiemannZeta.GuthMaynard
