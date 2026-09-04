import GafniTao.WooleyThreeFactorHolder

/-!
# Two-factor finite Hölder interpolation

This is the finite counting-measure form repeatedly used in Wooley Sections
8 and 9.  It is proved through Mathlib's `ENNReal` Hölder theorem and then
transported to nonnegative real summands.
-/

open Finset
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem wooley_two_factor_holder_ennreal
    {ι : Type*} (t : Finset ι) (f g : ι → ℝ≥0∞)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ i ∈ t, f i ^ u * g i ^ (1 - u)) ≤
      (∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u) := by
  classical
  let subF : Fintype {i : ι // i ∈ t} := Finset.fintypeCoeSort t
  letI : Fintype {i : ι // i ∈ t} := subF
  letI : MeasurableSpace {i : ι // i ∈ t} := ⊤
  let fs : Fin 2 → {i : ι // i ∈ t} → ℝ≥0∞ :=
    fun j x => Fin.cases (f x.1) (fun _ => g x.1) j
  let exps : Fin 2 → ℝ := ![u, 1 - u]
  have hmeas : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      AEMeasurable (fs j)
        (MeasureTheory.Measure.count : MeasureTheory.Measure {i : ι // i ∈ t}) := by
    intro j hj
    exact Measurable.aemeasurable (measurable_of_countable _)
  have hexpsum : ∑ j ∈ (Finset.univ : Finset (Fin 2)), exps j = 1 := by
    simp [Fin.sum_univ_succ, exps]
  have hexpnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ exps j := by
    intro j hj
    fin_cases j <;> simp [exps, hu0, hu1]
  have h := ENNReal.lintegral_prod_norm_pow_le
    (μ := (MeasureTheory.Measure.count :
      MeasureTheory.Measure {i : ι // i ∈ t}))
    (Finset.univ : Finset (Fin 2)) hmeas hexpsum hexpnonneg
  have hmem : ∀ i : ι, i ∈ t ↔ i ∈ t := fun _ => Iff.rfl
  rw [Finset.sum_subtype (F := subF) t hmem
      (fun i => f i ^ u * g i ^ (1 - u)),
    Finset.sum_subtype (F := subF) t hmem f,
    Finset.sum_subtype (F := subF) t hmem g]
  simpa [fs, exps, MeasureTheory.lintegral_count,
    tsum_fintype, Fin.sum_univ_succ, Fin.prod_univ_succ] using h

theorem wooley_two_factor_holder_real
    {ι : Type*} (t : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ t, 0 ≤ f i) (hg : ∀ i ∈ t, 0 ≤ g i)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ i ∈ t, f i ^ u * g i ^ (1 - u)) ≤
      (∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u) := by
  let F : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (f i)
  let G : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (g i)
  have hholder := wooley_two_factor_holder_ennreal t F G hu0 hu1
  have hOne : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hterm (i : ι) (hi : i ∈ t) :
      ENNReal.ofReal (f i ^ u * g i ^ (1 - u)) =
        F i ^ u * G i ^ (1 - u) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hf i hi) _)]
    simp only [F, G]
    rw [← ENNReal.ofReal_rpow_of_nonneg (hf i hi) hu0,
      ← ENNReal.ofReal_rpow_of_nonneg (hg i hi) hOne]
  have hsum (h : ι → ℝ) (hh : ∀ i ∈ t, 0 ≤ h i) :
      ENNReal.ofReal (∑ i ∈ t, h i) =
        ∑ i ∈ t, ENNReal.ofReal (h i) :=
    ENNReal.ofReal_sum_of_nonneg hh
  have hleft : 0 ≤ ∑ i ∈ t, f i ^ u * g i ^ (1 - u) :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (Real.rpow_nonneg (hf i hi) _)
        (Real.rpow_nonneg (hg i hi) _)
  have hsumF : 0 ≤ ∑ i ∈ t, f i := Finset.sum_nonneg hf
  have hsumG : 0 ≤ ∑ i ∈ t, g i := Finset.sum_nonneg hg
  have hright :
      0 ≤ (∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u) := by
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hright).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi =>
    mul_nonneg (Real.rpow_nonneg (hf i hi) _)
      (Real.rpow_nonneg (hg i hi) _))]
  have hterms :
      (∑ i ∈ t, ENNReal.ofReal (f i ^ u * g i ^ (1 - u))) =
        ∑ i ∈ t, F i ^ u * G i ^ (1 - u) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  rw [hterms, ENNReal.ofReal_mul (Real.rpow_nonneg hsumF _),
    ← ENNReal.ofReal_rpow_of_nonneg hsumF hu0,
    ← ENNReal.ofReal_rpow_of_nonneg hsumG hOne,
    hsum f hf, hsum g hg]
  exact hholder

#print axioms wooley_two_factor_holder_ennreal
#print axioms wooley_two_factor_holder_real

end

end GafniTao
