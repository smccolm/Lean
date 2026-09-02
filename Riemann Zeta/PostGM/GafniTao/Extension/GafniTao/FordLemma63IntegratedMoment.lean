import GafniTao.FordLemma63SZeroMoment

/-!
# Ford Lemma 6.3: integration of the `S₀` majorant

The integration domain is the literal half-open unit cube used in Ford's
equation (1.3).  We dominate it by the closed cube only to discharge
Bochner-integrability; no endpoint or measure convention is changed.
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordUnitCube (k : ℕ) : Set (Fin k → ℝ) :=
  {β | ∀ j, β j ∈ Set.Ioc (0 : ℝ) 1}

def fordClosedUnitCube (k : ℕ) : Set (Fin k → ℝ) :=
  {β | ∀ j, β j ∈ Set.Icc (0 : ℝ) 1}

theorem fordUnitCube_subset_closed (k : ℕ) :
    fordUnitCube k ⊆ fordClosedUnitCube k := by
  intro β hβ j
  exact ⟨(hβ j).1.le, (hβ j).2⟩

theorem isCompact_fordClosedUnitCube (k : ℕ) :
    IsCompact (fordClosedUnitCube k) := by
  simpa [fordClosedUnitCube, Set.pi] using
    (isCompact_univ_pi fun _ : Fin k => isCompact_Icc :
      IsCompact (Set.pi Set.univ fun _ : Fin k => Set.Icc (0 : ℝ) 1))

theorem measurableSet_fordUnitCube (k : ℕ) : MeasurableSet (fordUnitCube k) := by
  simpa [fordUnitCube, Set.pi] using
    (MeasurableSet.pi countable_univ
      (fun _ : Fin k => fun _ => measurableSet_Ioc) :
        MeasurableSet (Set.pi Set.univ fun _ : Fin k => Set.Ioc (0 : ℝ) 1))

theorem continuous_fordLemma63PolynomialSum (k Q : ℕ) :
    Continuous (fordLemma63PolynomialSum k Q) := by
  unfold fordLemma63PolynomialSum fordLemma63PolynomialPhase fordAdditiveCharacter
  fun_prop

theorem continuous_fordLemma63SZero (k M : ℕ) :
    Continuous (fordLemma63SZero k M) := by
  unfold fordLemma63SZero fordLemma63SZeroTail
  exact (continuous_fordLemma63PolynomialSum k M).norm.add
    (continuous_const.mul
      (continuous_finsetSum _ fun q _ =>
        (continuous_fordLemma63PolynomialSum k (q + 1)).norm))

theorem integrableOn_fordLemma63SZero_pow (k M r : ℕ) :
    IntegrableOn (fun β : Fin k → ℝ => fordLemma63SZero k M β ^ r)
      (fordUnitCube k) := by
  have hc : Continuous (fun β : Fin k → ℝ => fordLemma63SZero k M β ^ r) :=
    (continuous_fordLemma63SZero k M).pow r
  exact (hc.continuousOn.integrableOn_compact (isCompact_fordClosedUnitCube k)).mono_set
    (fordUnitCube_subset_closed k)

theorem integrableOn_fordLemma63PolynomialSum_norm_pow (k Q r : ℕ) :
    IntegrableOn
      (fun β : Fin k → ℝ => ‖fordLemma63PolynomialSum k Q β‖ ^ r)
      (fordUnitCube k) := by
  have hc : Continuous
      (fun β : Fin k → ℝ => ‖fordLemma63PolynomialSum k Q β‖ ^ r) :=
    (continuous_fordLemma63PolynomialSum k Q).norm.pow r
  exact (hc.continuousOn.integrableOn_compact (isCompact_fordClosedUnitCube k)).mono_set
    (fordUnitCube_subset_closed k)

theorem fordLemma63_integral_SZero_power_le
    {k M r : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    (∫ β : Fin k → ℝ in fordUnitCube k, fordLemma63SZero k M β ^ r) ≤
      ∫ β : Fin k → ℝ in fordUnitCube k,
        (2 : ℝ) ^ (2 * r) *
          (‖fordLemma63PolynomialSum k M β‖ ^ r +
            (1 / (M : ℝ)) *
              ∑ q ∈ Finset.range (M - 1),
                ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
  have hf := integrableOn_fordLemma63SZero_pow k M r
  have hgCont : Continuous (fun β : Fin k → ℝ =>
      (2 : ℝ) ^ (2 * r) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r)) := by
    exact continuous_const.mul
      ((continuous_fordLemma63PolynomialSum k M).norm.pow r |>.add
        (continuous_const.mul
          (continuous_finsetSum _ fun q _ =>
            (continuous_fordLemma63PolynomialSum k (q + 1)).norm.pow r)))
  have hg : IntegrableOn (fun β : Fin k → ℝ =>
      (2 : ℝ) ^ (2 * r) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r)) (fordUnitCube k) :=
    (hgCont.continuousOn.integrableOn_compact (isCompact_fordClosedUnitCube k)).mono_set
      (fordUnitCube_subset_closed k)
  exact setIntegral_mono_on hf hg (measurableSet_fordUnitCube k)
    (fun β hβ => fordLemma63SZero_power_le hM hr)

theorem fordLemma63_integral_SZero_power_le_sharp
    {k M r : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    (∫ β : Fin k → ℝ in fordUnitCube k, fordLemma63SZero k M β ^ r) ≤
      ∫ β : Fin k → ℝ in fordUnitCube k,
        (2 : ℝ) ^ (r - 1) *
          (‖fordLemma63PolynomialSum k M β‖ ^ r +
            (2 : ℝ) ^ r * (1 / (M : ℝ)) *
              ∑ q ∈ Finset.range (M - 1),
                ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
  have hf := integrableOn_fordLemma63SZero_pow k M r
  have hgCont : Continuous (fun β : Fin k → ℝ =>
      (2 : ℝ) ^ (r - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (2 : ℝ) ^ r * (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r)) := by
    exact continuous_const.mul
      ((continuous_fordLemma63PolynomialSum k M).norm.pow r |>.add
        (continuous_const.mul
          (continuous_finsetSum _ fun q _ =>
            (continuous_fordLemma63PolynomialSum k (q + 1)).norm.pow r)))
  have hg : IntegrableOn (fun β : Fin k → ℝ =>
      (2 : ℝ) ^ (r - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (2 : ℝ) ^ r * (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r)) (fordUnitCube k) :=
    (hgCont.continuousOn.integrableOn_compact (isCompact_fordClosedUnitCube k)).mono_set
      (fordUnitCube_subset_closed k)
  exact setIntegral_mono_on hf hg (measurableSet_fordUnitCube k)
    (fun β hβ => fordLemma63SZero_power_le_sharp hM hr)

#print axioms fordUnitCube_subset_closed
#print axioms isCompact_fordClosedUnitCube
#print axioms continuous_fordLemma63PolynomialSum
#print axioms integrableOn_fordLemma63SZero_pow
#print axioms fordLemma63_integral_SZero_power_le
#print axioms fordLemma63_integral_SZero_power_le_sharp

end

end GafniTao
