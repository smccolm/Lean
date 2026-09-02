import GafniTao.FordGeneralLocalCountAsymptotic
import GafniTao.RightEdge

/-!
# Partial summation for Ford's local inverse-square zero sum

Ford's lemma following the local disk count applies partial summation to the
actual distances `|1 + it - rho|`.  We retain a fixed outer disk and expose
the annulus endpoint convention.  The cumulative function below is therefore
a literal finite multiplicity count, not an independently supplied counting
function.
-/

open Complex Finset MeasureTheory Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Distance from Ford's physical centre `1 + it`. -/
noncomputable def fordLocalDistance (t : ℝ) (rho : ℂ) : ℝ :=
  ‖(1 : ℂ) + (t : ℂ) * I - rho‖

/-- The literal closed-inner/open-outer annulus used for the finite
partial-summation identity.  The outer condition is already carried by
`fordLocalDiskZeros t q`. -/
noncomputable def fordLocalAnnulus (t v q : ℝ) : Finset ℂ :=
  (fordLocalDiskZeros t q).filter fun rho => v ≤ fordLocalDistance t rho

/-- Multiplicity in the part of the fixed annulus lying strictly inside
radius `u`.  The strict endpoint matches the `Ioc` indicator in the common
interval representation of the integral. -/
noncomputable def fordLocalAnnulusCumulative
    (t v q u : ℝ) : ℕ :=
  ∑ rho ∈ (fordLocalAnnulus t v q).filter
      (fun rho => fordLocalDistance t rho < u),
    analyticVanishingOrder riemannZeta rho

/-- The exact multiplicity-weighted inverse-square sum over the local
annulus. -/
noncomputable def fordLocalAnnularInverseSquare
    (t v q : ℝ) : ℝ :=
  ∑ rho ∈ fordLocalAnnulus t v q,
    (analyticVanishingOrder riemannZeta rho : ℝ) /
      fordLocalDistance t rho ^ 2

theorem mem_fordLocalDiskZeros_of_mem_outer_of_distance_le
    {t q u : ℝ} {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t q)
    (hdist : fordLocalDistance t rho ≤ u) :
    rho ∈ fordLocalDiskZeros t u := by
  have hdata := mem_fordLocalDiskZeros_data hrho
  have himDist : |t - rho.im| ≤ fordLocalDistance t rho := by
    simpa [fordLocalDistance] using
      Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * I - rho)
  have himAbs : |rho.im| ≤ |t| + u := by
    calc
      |rho.im| = |t - (t - rho.im)| := by ring_nf
      _ ≤ |t| + |t - rho.im| := abs_sub _ _
      _ ≤ |t| + u := by linarith
  rw [mem_fordLocalDiskZeros_iff]
  constructor
  · change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (- (|t| + u)) (|t| + u)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (- (|t| + u)) (|t| + u) rho).mpr ?_, hdata.1⟩
    exact ⟨hdata.2.1, hdata.2.2.1,
      (abs_le.mp himAbs).1, (abs_le.mp himAbs).2⟩
  · exact hdist

/-- The annular cumulative multiplicity is bounded by Ford's actual local
disk count at the same physical radius. -/
theorem fordLocalAnnulusCumulative_le_diskCount
    {t v q u : ℝ} :
    fordLocalAnnulusCumulative t v q u ≤
      fordLocalDiskZeroCount t u := by
  classical
  unfold fordLocalAnnulusCumulative fordLocalDiskZeroCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    simp only [Finset.mem_filter] at hrho
    exact mem_fordLocalDiskZeros_of_mem_outer_of_distance_le
      (Finset.mem_filter.mp hrho.1).1 hrho.2.le
  · intro _ _ _
    exact Nat.zero_le _

/-- The outer endpoint multiplicity in the annulus is bounded by the actual
local disk count. -/
theorem fordLocalAnnulusMultiplicity_le_diskCount
    {t v q : ℝ} :
    ∑ rho ∈ fordLocalAnnulus t v q,
        analyticVanishingOrder riemannZeta rho ≤
      fordLocalDiskZeroCount t q := by
  classical
  unfold fordLocalAnnulus fordLocalDiskZeroCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- The elementary inverse-square layer identity used in Ford's partial
summation. -/
theorem inv_sq_eq_endpoint_add_integral
    {d q : ℝ} (hd : 0 < d) (hdq : d ≤ q) :
    1 / d ^ 2 = 1 / q ^ 2 +
      ∫ u : ℝ in d..q, 2 / u ^ 3 := by
  have hq : 0 < q := hd.trans_le hdq
  have hderiv : ∀ u : ℝ, u ∈ Set.uIcc d q →
      HasDerivAt (fun x : ℝ => -1 / x ^ 2) (2 / u ^ 3) u := by
    intro u hu
    rw [uIcc_of_le hdq] at hu
    have hu0 : u ≠ 0 := ne_of_gt (hd.trans_le hu.1)
    convert ((hasDerivAt_inv hu0).pow 2).neg using 1
    · ext x
      simp [div_eq_mul_inv]
    · norm_num
      field_simp [hu0]
  have hint : IntervalIntegrable (fun u : ℝ => 2 / u ^ 3)
      volume d q := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hdq] at hu
      exact pow_ne_zero 3 (ne_of_gt (hd.trans_le hu.1))
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := d) (b := q) (f := fun x : ℝ => -1 / x ^ 2)
    (f' := fun u : ℝ => 2 / u ^ 3) hderiv hint
  rw [hInt]
  ring

/-- General common-interval representation of an upper subinterval
integral. -/
theorem intervalIntegral_indicator_Ioc_between
    {f : ℝ → ℝ} {v d q : ℝ} (hd : d ∈ Icc v q) :
    (∫ u : ℝ in v..q, (Ioc d q).indicator f u) =
      ∫ u : ℝ in d..q, f u := by
  rw [intervalIntegral.integral_of_le (hd.1.trans hd.2),
    intervalIntegral.integral_of_le hd.2,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  rw [show Ioc d q ∩ Ioc v q = Ioc d q by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hdu, huq⟩, _, _⟩
      exact ⟨hdu, huq⟩
    · rintro ⟨hdu, huq⟩
      exact ⟨⟨hdu, huq⟩, hd.1.trans_lt hdu, huq⟩]

/-- Exact finite pre-interchange form of Ford's inverse-square partial
summation. -/
theorem fordLocalAnnularInverseSquare_eq_endpoint_add_sum_integrals
    {t v q : ℝ} (hv : 0 < v) :
    fordLocalAnnularInverseSquare t v q =
      (fordLocalAnnulus t v q).sum
          (fun rho => (analyticVanishingOrder riemannZeta rho : ℝ)) /
        q ^ 2 +
      ∑ rho ∈ fordLocalAnnulus t v q,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (∫ u : ℝ in fordLocalDistance t rho..q, 2 / u ^ 3) := by
  classical
  unfold fordLocalAnnularInverseSquare
  have hdist (rho : ℂ) (hrho : rho ∈ fordLocalAnnulus t v q) :
      0 < fordLocalDistance t rho ∧ fordLocalDistance t rho ≤ q := by
    have hmem := Finset.mem_filter.mp hrho
    have houter := (mem_fordLocalDiskZeros_iff.mp hmem.1).2
    exact ⟨hv.trans_le hmem.2, houter⟩
  calc
    (∑ rho ∈ fordLocalAnnulus t v q,
        (analyticVanishingOrder riemannZeta rho : ℝ) /
          fordLocalDistance t rho ^ 2) =
      ∑ rho ∈ fordLocalAnnulus t v q,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (1 / q ^ 2 +
            ∫ u : ℝ in fordLocalDistance t rho..q, 2 / u ^ 3) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hid := inv_sq_eq_endpoint_add_integral
        (hdist rho hrho).1 (hdist rho hrho).2
      calc
        (analyticVanishingOrder riemannZeta rho : ℝ) /
            fordLocalDistance t rho ^ 2 =
          (analyticVanishingOrder riemannZeta rho : ℝ) *
            (1 / fordLocalDistance t rho ^ 2) := by ring
        _ = (analyticVanishingOrder riemannZeta rho : ℝ) *
            (1 / q ^ 2 +
              ∫ u : ℝ in fordLocalDistance t rho..q, 2 / u ^ 3) := by
          rw [hid]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ x ∈ fordLocalAnnulus t v q,
            (analyticVanishingOrder riemannZeta x : ℝ) * (1 / q ^ 2)) =
          (∑ x ∈ fordLocalAnnulus t v q,
            (analyticVanishingOrder riemannZeta x : ℝ)) *
              (1 / q ^ 2) :=
          (Finset.sum_mul (fordLocalAnnulus t v q)
            (fun x => (analyticVanishingOrder riemannZeta x : ℝ))
            (1 / q ^ 2)).symm
        _ = (∑ x ∈ fordLocalAnnulus t v q,
            (analyticVanishingOrder riemannZeta x : ℝ)) / q ^ 2 := by ring

/-- Exact single-integral form of the local inverse-square sum.  This is the
literal Stieltjes/Abel bridge: the integrand contains the actual finite
analytic-multiplicity count generated by the zero set. -/
theorem fordLocalAnnularInverseSquare_eq_cumulative_integral
    {t v q : ℝ} (hv : 0 < v) (hvq : v ≤ q) :
    fordLocalAnnularInverseSquare t v q =
      (fordLocalAnnulus t v q).sum
          (fun rho => (analyticVanishingOrder riemannZeta rho : ℝ)) /
        q ^ 2 +
      ∫ u : ℝ in v..q,
        (2 / u ^ 3) * (fordLocalAnnulusCumulative t v q u : ℝ) := by
  classical
  rw [fordLocalAnnularInverseSquare_eq_endpoint_add_sum_integrals hv]
  congr 1
  let Z := fordLocalAnnulus t v q
  let f : ℝ → ℝ := fun u => 2 / u ^ 3
  have hf : IntervalIntegrable f volume v q := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hvq] at hu
      exact pow_ne_zero 3 (ne_of_gt (hv.trans_le hu.1))
  have hd (rho : ℂ) (hrho : rho ∈ Z) :
      fordLocalDistance t rho ∈ Icc v q := by
    have hmem := Finset.mem_filter.mp hrho
    exact ⟨hmem.2, (mem_fordLocalDiskZeros_iff.mp hmem.1).2⟩
  have hIndicatorIntegrable (rho : ℂ) (hrho : rho ∈ Z) :
      IntervalIntegrable
        (fun u => (analyticVanishingOrder riemannZeta rho : ℝ) *
          (Ioc (fordLocalDistance t rho) q).indicator f u)
        volume v q := by
    apply IntervalIntegrable.const_mul _
    constructor
    · exact hf.1.indicator measurableSet_Ioc
    · exact hf.2.indicator measurableSet_Ioc
  change (∑ rho ∈ Z,
      (analyticVanishingOrder riemannZeta rho : ℝ) *
        (∫ u : ℝ in fordLocalDistance t rho..q, f u)) = _
  calc
    _ = ∑ rho ∈ Z, ∫ u : ℝ in v..q,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (Ioc (fordLocalDistance t rho) q).indicator f u := by
      apply Finset.sum_congr rfl
      intro rho hrho
      calc
        (analyticVanishingOrder riemannZeta rho : ℝ) *
            (∫ u : ℝ in fordLocalDistance t rho..q, f u) =
          (analyticVanishingOrder riemannZeta rho : ℝ) *
            (∫ u : ℝ in v..q,
              (Ioc (fordLocalDistance t rho) q).indicator f u) := by
            rw [intervalIntegral_indicator_Ioc_between (hd rho hrho)]
        _ = ∫ u : ℝ in v..q,
            (analyticVanishingOrder riemannZeta rho : ℝ) *
              (Ioc (fordLocalDistance t rho) q).indicator f u := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ u : ℝ in v..q, ∑ rho ∈ Z,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (Ioc (fordLocalDistance t rho) q).indicator f u := by
      rw [intervalIntegral.integral_finsetSum]
      exact fun rho hrho => hIndicatorIntegrable rho hrho
    _ = ∫ u : ℝ in v..q,
        f u * (fordLocalAnnulusCumulative t v q u : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hvq] at hu
      change (∑ rho ∈ Z,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (Ioc (fordLocalDistance t rho) q).indicator f u) =
        f u * ↑(∑ rho ∈ Z.filter
          (fun rho => fordLocalDistance t rho < u),
            analyticVanishingOrder riemannZeta rho)
      simp only [Nat.cast_sum, Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      by_cases hdist : fordLocalDistance t rho < u
      · simp [Set.indicator, hdist, hu.2, mul_comm]
      · simp [Set.indicator, hdist]

/-- The literal cumulative integrand is interval integrable.  This is proved
from its finite indicator representation, rather than inferred from the
notation for the interval integral. -/
theorem intervalIntegrable_fordLocalAnnulusCumulativeKernel
    {t v q : ℝ} (hv : 0 < v) (hvq : v ≤ q) :
    IntervalIntegrable
      (fun u : ℝ => (2 / u ^ 3) *
        (fordLocalAnnulusCumulative t v q u : ℝ)) volume v q := by
  classical
  let Z := fordLocalAnnulus t v q
  let f : ℝ → ℝ := fun u => 2 / u ^ 3
  have hf : IntervalIntegrable f volume v q := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hvq] at hu
      exact pow_ne_zero 3 (ne_of_gt (hv.trans_le hu.1))
  have hterm (rho : ℂ) : IntervalIntegrable
      (fun u => (analyticVanishingOrder riemannZeta rho : ℝ) *
        (Ioc (fordLocalDistance t rho) q).indicator f u) volume v q := by
    apply IntervalIntegrable.const_mul _
    constructor
    · exact hf.1.indicator measurableSet_Ioc
    · exact hf.2.indicator measurableSet_Ioc
  have hsum : IntervalIntegrable
      (fun u => ∑ rho ∈ Z,
        (analyticVanishingOrder riemannZeta rho : ℝ) *
          (Ioc (fordLocalDistance t rho) q).indicator f u) volume v q := by
    induction Z using Finset.induction_on with
    | empty => simp
    | @insert rho Z hrho ih =>
        simp_rw [Finset.sum_insert hrho]
        exact (hterm rho).add ih
  apply hsum.congr
  intro u hu
  rw [uIoc_of_le hvq] at hu
  change (∑ rho ∈ Z,
      (analyticVanishingOrder riemannZeta rho : ℝ) *
        (Ioc (fordLocalDistance t rho) q).indicator f u) =
    f u * ↑(∑ rho ∈ Z.filter
      (fun rho => fordLocalDistance t rho < u),
        analyticVanishingOrder riemannZeta rho)
  simp only [Nat.cast_sum, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hdist : fordLocalDistance t rho < u
  · simp [Set.indicator, hdist, hu.2, mul_comm]
  · simp [Set.indicator, hdist]

/-- The continuous Richert-scale inverse-square integrand obtained by
inserting Ford's proved local count. -/
noncomputable def fordGeneralLocalInverseSquareIntegrand
    (A B t u : ℝ) : ℝ :=
  (2 / u ^ 3) * fordGeneralLocalCountConstant *
    fordGeneralLocalCountScale A B t u

theorem intervalIntegrable_fordGeneralLocalInverseSquareIntegrand
    {A B t v q : ℝ} (hv : 0 < v) (hvq : v ≤ q) :
    IntervalIntegrable
      (fordGeneralLocalInverseSquareIntegrand A B t) volume v q := by
  apply ContinuousOn.intervalIntegrable
  unfold fordGeneralLocalInverseSquareIntegrand
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro u hu
        rw [uIcc_of_le hvq] at hu
        exact pow_ne_zero 3 (ne_of_gt (hv.trans_le hu.1))
    · exact continuousOn_const
  · unfold fordGeneralLocalCountScale
    have hlog : ContinuousOn Real.log (Set.uIcc v q) := by
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [uIcc_of_le hvq] at hu
      exact ne_of_gt (hv.trans_le hu.1)
    have hrpow : ContinuousOn
        (fun u : ℝ => (2 * u) ^ (3 / 2 : ℝ)) (Set.uIcc v q) := by
      apply (continuousOn_const.mul continuousOn_id).rpow_const
      intro _ _
      exact Or.inr (by norm_num)
    have hterm : ContinuousOn
        (fun u : ℝ => B * (2 * u) ^ (3 / 2 : ℝ) * Real.log t)
        (Set.uIcc v q) :=
      (continuousOn_const.mul hrpow).mul continuousOn_const
    exact (((continuousOn_const.add continuousOn_const).sub hlog).add
      continuousOn_const).add hterm

/-- Ford's local inverse-square sum is bounded by the integral of the actual
Richert-scale local count.  All terms are tied to the same physical zeros and
the same centre `1+it`. -/
theorem fordLocalAnnularInverseSquare_le_general_integral
    {A B t v q : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (ht : 100 ≤ t)
    (hv : 0 < v) (hvq : v ≤ q) (hq : q ≤ 1 / 4) :
    fordLocalAnnularInverseSquare t v q ≤
      fordGeneralLocalCountConstant *
          fordGeneralLocalCountScale A B t q / q ^ 2 +
        ∫ u : ℝ in v..q,
          fordGeneralLocalInverseSquareIntegrand A B t u := by
  rw [fordLocalAnnularInverseSquare_eq_cumulative_integral hv hvq]
  apply add_le_add
  · have hcount := fordLocalAnnulusMultiplicity_le_diskCount
        (t := t) (v := v) (q := q)
    have hlocal := fordLocalDiskZeroCount_le_general_scale
      hFord hA hB ht (hv.trans_le hvq) hq
    have hqSq : 0 ≤ q ^ 2 := sq_nonneg q
    have hcountReal :
        (∑ rho ∈ fordLocalAnnulus t v q,
          (analyticVanishingOrder riemannZeta rho : ℝ)) ≤
          (fordLocalDiskZeroCount t q : ℝ) := by
      exact_mod_cast hcount
    calc
      (∑ rho ∈ fordLocalAnnulus t v q,
          (analyticVanishingOrder riemannZeta rho : ℝ)) / q ^ 2 ≤
          (fordLocalDiskZeroCount t q : ℝ) / q ^ 2 := by
        gcongr
        exact hcountReal
      _ ≤ fordGeneralLocalCountConstant *
          fordGeneralLocalCountScale A B t q / q ^ 2 := by
        exact div_le_div_of_nonneg_right hlocal.le hqSq
  · refine intervalIntegral.integral_mono_on hvq
      (intervalIntegrable_fordLocalAnnulusCumulativeKernel
        (t := t) hv hvq)
      (intervalIntegrable_fordGeneralLocalInverseSquareIntegrand
        (A := A) (B := B) (t := t) hv hvq) ?_
    intro u hu
    have huPos : 0 < u := hv.trans_le hu.1
    have huUpper : u ≤ 1 / 4 := hu.2.trans hq
    have hcount := fordLocalAnnulusCumulative_le_diskCount
      (t := t) (v := v) (q := q) (u := u)
    have hlocal := fordLocalDiskZeroCount_le_general_scale
      hFord hA hB ht huPos huUpper
    have hkernel : 0 ≤ 2 / u ^ 3 := by positivity
    unfold fordGeneralLocalInverseSquareIntegrand
    calc
      (2 / u ^ 3) * (fordLocalAnnulusCumulative t v q u : ℝ) ≤
          (2 / u ^ 3) * (fordLocalDiskZeroCount t u : ℝ) := by
        gcongr
        exact_mod_cast hcount
      _ ≤ (2 / u ^ 3) *
          (fordGeneralLocalCountConstant *
            fordGeneralLocalCountScale A B t u) := by
        exact mul_le_mul_of_nonneg_left hlocal.le hkernel
      _ = (2 / u ^ 3) * fordGeneralLocalCountConstant *
          fordGeneralLocalCountScale A B t u := by ring

#print axioms fordLocalAnnularInverseSquare_eq_cumulative_integral
#print axioms fordLocalAnnularInverseSquare_le_general_integral

end

end GafniTao
