import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The three-factor Hölder interpolation in Wooley equation (6.8)

The difficult Hölder step in the initial conditioning argument is an
interpolation between the unweighted pair count and the two oppositely
oriented mixed moments.  This file proves the finite nonnegative inequality
directly, with all three exponents visible.
-/

open Finset
open scoped BigOperators ENNReal
open MeasureTheory

namespace GafniTao

noncomputable section

/-- Finite three-factor Hölder, stated in the exact weighted-power form used
in Wooley (6.8). -/
theorem wooley_three_factor_holder_ennreal
    {ι : Type*} (t : Finset ι) (f₀ f₁ f₂ : ι → ℝ≥0∞)
    (a₀ a₁ a₂ : ℝ) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hsum : a₀ + a₁ + a₂ = 1) :
    (∑ i ∈ t, f₀ i ^ a₀ * f₁ i ^ a₁ * f₂ i ^ a₂) ≤
      (∑ i ∈ t, f₀ i) ^ a₀ *
        (∑ i ∈ t, f₁ i) ^ a₁ *
          (∑ i ∈ t, f₂ i) ^ a₂ := by
  classical
  let subF : Fintype {i : ι // i ∈ t} :=
    Finset.fintypeCoeSort t
  letI : Fintype {i : ι // i ∈ t} := subF
  letI : MeasurableSpace {i : ι // i ∈ t} := ⊤
  let fs : Fin 3 → {i : ι // i ∈ t} → ℝ≥0∞ := fun j x =>
    Fin.cases (f₀ x.1)
      (fun j' => Fin.cases (f₁ x.1) (fun _ => f₂ x.1) j') j
  let exps : Fin 3 → ℝ := ![a₀, a₁, a₂]
  have hmeas : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      AEMeasurable (fs j)
        (Measure.count : Measure {i : ι // i ∈ t}) := by
    intro j hj
    exact Measurable.aemeasurable (measurable_of_countable _)
  have hexpsum : ∑ j ∈ (Finset.univ : Finset (Fin 3)), exps j = 1 := by
    simpa [Fin.sum_univ_succ, exps, add_assoc] using hsum
  have hexpnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ exps j := by
    intro j hj
    fin_cases j <;> simp [exps, ha₀, ha₁, ha₂]
  have h := ENNReal.lintegral_prod_norm_pow_le
    (μ := (Measure.count : Measure {i : ι // i ∈ t}))
    (Finset.univ : Finset (Fin 3)) hmeas hexpsum hexpnonneg
  have hmem : ∀ i : ι, i ∈ t ↔ i ∈ t := fun _ => Iff.rfl
  rw [Finset.sum_subtype (F := subF) t hmem
      (fun i => f₀ i ^ a₀ * f₁ i ^ a₁ * f₂ i ^ a₂),
    Finset.sum_subtype (F := subF) t hmem f₀,
    Finset.sum_subtype (F := subF) t hmem f₁,
    Finset.sum_subtype (F := subF) t hmem f₂]
  simpa [fs, exps, lintegral_count, tsum_fintype,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc] using h

/-- The critical specialization of three-factor Hölder.  The two last
factors receive exponent `1/s`, while the mass factor receives
`(s-2)/s`; raising to `s` gives exactly the exponents in (6.8). -/
theorem wooley_three_factor_holder_critical_ennreal
    {ι : Type*} (t : Finset ι) (f₀ f₁ f₂ : ι → ℝ≥0∞)
    {s : ℕ} (hs : 2 ≤ s) :
    (∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) *
            f₂ i ^ (1 / (s : ℝ))) ^ (s : ℝ) ≤
      (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) *
          (∑ i ∈ t, f₂ i) := by
  have hsReal : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hsTwo : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have ha₀ : 0 ≤ ((s : ℝ) - 2) / (s : ℝ) :=
    div_nonneg (sub_nonneg.mpr hsTwo) hsReal.le
  have ha₁ : 0 ≤ 1 / (s : ℝ) := by positivity
  have hexp : ((s : ℝ) - 2) / (s : ℝ) +
      1 / (s : ℝ) + 1 / (s : ℝ) = 1 := by
    field_simp
    ring
  have hholder := wooley_three_factor_holder_ennreal t f₀ f₁ f₂
    (((s : ℝ) - 2) / (s : ℝ)) (1 / (s : ℝ)) (1 / (s : ℝ))
    ha₀ ha₁ ha₁ hexp
  have hraised := ENNReal.rpow_le_rpow hholder
    (by exact_mod_cast (Nat.zero_le s) : (0 : ℝ) ≤ s)
  calc
    (∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) *
            f₂ i ^ (1 / (s : ℝ))) ^ (s : ℝ) ≤
      (((∑ i ∈ t, f₀ i) ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (∑ i ∈ t, f₁ i) ^ (1 / (s : ℝ)) *
            (∑ i ∈ t, f₂ i) ^ (1 / (s : ℝ)))) ^ (s : ℝ) := hraised
    _ = (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) *
          (∑ i ∈ t, f₂ i) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hsReal.le,
        ENNReal.mul_rpow_of_nonneg _ _ hsReal.le]
      simp only [← ENNReal.rpow_mul]
      have hsNe : (s : ℝ) ≠ 0 := ne_of_gt hsReal
      congr 1
      · congr 1
        · congr 1
          field_simp
        · field_simp
          simp
      · field_simp
        simp

/-- Real-valued form of the critical three-factor interpolation.  Keeping
the factors nonnegative is exactly what permits a lossless passage through
`ENNReal.ofReal`; this is the form used for the norms and residue masses in
Wooley (6.8). -/
theorem wooley_three_factor_holder_critical_real
    {ι : Type*} (t : Finset ι) (f₀ f₁ f₂ : ι → ℝ)
    (hf₀ : ∀ i ∈ t, 0 ≤ f₀ i)
    (hf₁ : ∀ i ∈ t, 0 ≤ f₁ i)
    (hf₂ : ∀ i ∈ t, 0 ≤ f₂ i)
    {s : ℕ} (hs : 2 ≤ s) :
    (∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) *
            f₂ i ^ (1 / (s : ℝ))) ^ (s : ℝ) ≤
      (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) *
          (∑ i ∈ t, f₂ i) := by
  have hsReal : (0 : ℝ) < s := by
    exact_mod_cast (by omega : 0 < s)
  have hsTwo : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have ha₀ : 0 ≤ ((s : ℝ) - 2) / (s : ℝ) :=
    div_nonneg (sub_nonneg.mpr hsTwo) hsReal.le
  have ha₁ : 0 ≤ 1 / (s : ℝ) := by positivity
  let F₀ : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (f₀ i)
  let F₁ : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (f₁ i)
  let F₂ : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (f₂ i)
  have hholder := wooley_three_factor_holder_critical_ennreal
    t F₀ F₁ F₂ hs
  have hterm (i : ι) (hi : i ∈ t) :
      ENNReal.ofReal
          (f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
            f₁ i ^ (1 / (s : ℝ)) *
              f₂ i ^ (1 / (s : ℝ))) =
        F₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          F₁ i ^ (1 / (s : ℝ)) *
            F₂ i ^ (1 / (s : ℝ)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg
        (Real.rpow_nonneg (hf₀ i hi) _)
        (Real.rpow_nonneg (hf₁ i hi) _)),
      ENNReal.ofReal_mul (Real.rpow_nonneg (hf₀ i hi) _)]
    simp only [F₀, F₁, F₂]
    rw [← ENNReal.ofReal_rpow_of_nonneg (hf₀ i hi) ha₀,
      ← ENNReal.ofReal_rpow_of_nonneg (hf₁ i hi) ha₁,
      ← ENNReal.ofReal_rpow_of_nonneg (hf₂ i hi) ha₁]
  have hsum (f : ι → ℝ) (hf : ∀ i ∈ t, 0 ≤ f i) :
      ENNReal.ofReal (∑ i ∈ t, f i) =
        ∑ i ∈ t, ENNReal.ofReal (f i) :=
    ENNReal.ofReal_sum_of_nonneg hf
  have hleftNonneg :
      0 ≤ ∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) *
            f₂ i ^ (1 / (s : ℝ)) := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (hf₀ i hi) _)
          (Real.rpow_nonneg (hf₁ i hi) _))
        (Real.rpow_nonneg (hf₂ i hi) _)
  have hrightNonneg :
      0 ≤ (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) * (∑ i ∈ t, f₂ i) := by
    have hsum₀ : 0 ≤ ∑ i ∈ t, f₀ i :=
      Finset.sum_nonneg fun i hi => hf₀ i hi
    have hsum₁ : 0 ≤ ∑ i ∈ t, f₁ i :=
      Finset.sum_nonneg fun i hi => hf₁ i hi
    have hsum₂ : 0 ≤ ∑ i ∈ t, f₂ i :=
      Finset.sum_nonneg fun i hi => hf₂ i hi
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hrightNonneg).mp
  rw [← ENNReal.ofReal_rpow_of_nonneg hleftNonneg hsReal.le]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi =>
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hf₀ i hi) _)
        (Real.rpow_nonneg (hf₁ i hi) _))
      (Real.rpow_nonneg (hf₂ i hi) _))]
  have hsumTerm :
      (∑ i ∈ t, ENNReal.ofReal
        (f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ)))) =
        ∑ i ∈ t,
          F₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
            F₁ i ^ (1 / (s : ℝ)) * F₂ i ^ (1 / (s : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  rw [hsumTerm]
  rw [ENNReal.ofReal_mul (mul_nonneg
      (Real.rpow_nonneg (Finset.sum_nonneg fun i hi => hf₀ i hi) _)
      (Finset.sum_nonneg fun i hi => hf₁ i hi)),
    ENNReal.ofReal_mul (Real.rpow_nonneg
      (Finset.sum_nonneg fun i hi => hf₀ i hi) _),
    ← ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun i hi => hf₀ i hi)
      (sub_nonneg.mpr hsTwo), hsum f₀ hf₀, hsum f₁ hf₁, hsum f₂ hf₂]
  exact hholder

#print axioms wooley_three_factor_holder_critical_ennreal

#print axioms wooley_three_factor_holder_critical_real

#print axioms wooley_three_factor_holder_ennreal

end

end GafniTao
