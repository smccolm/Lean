import RiemannZeta.GuthMaynard.HughesYoungActiveMoment
import RiemannZeta.GuthMaynard.HughesYoungFiniteSquareBridge

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global active Hughes--Young opening

This file inserts the actual squared Maynard--Pratt Möbius coefficients into
the finite active dyadic contour identity.  The result is an exact pointwise
decomposition of the source fourth-moment integrand; no estimate is used in
this layer.
-/

noncomputable def hughesYoungMollifierPairTerm
    (T t : ℝ) (h k : ℕ) : ℂ :=
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t))

theorem continuous_hughesYoungMollifierPairTerm
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Continuous (fun t : ℝ => hughesYoungMollifierPairTerm T t h k) := by
  have hhpow : Continuous (fun t : ℝ =>
      (h : ℂ) ^ (-afeCriticalPoint t)) :=
    continuous_const_cpow_of_ne_zero (h : ℂ)
      (by exact_mod_cast (Nat.ne_of_gt hh)) (by
        unfold afeCriticalPoint
        fun_prop)
  have hkpow : Continuous (fun t : ℝ =>
      (k : ℂ) ^ (-afeCriticalPoint (-t))) :=
    continuous_const_cpow_of_ne_zero (k : ℂ)
      (by exact_mod_cast (Nat.ne_of_gt hk)) (by
        unfold afeCriticalPoint
        fun_prop)
  unfold hughesYoungMollifierPairTerm
  exact ((continuous_const.mul hhpow).mul continuous_const).mul hkpow

theorem norm_hughesYoungMollifierPairTerm_le
    (T t : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungMollifierPairTerm T t h k‖ ≤
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ := by
  have hhOne : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhpow : ‖(h : ℂ) ^ (-afeCriticalPoint t)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    apply Real.rpow_le_one_of_one_le_of_nonpos hhOne
    simp [afeCriticalPoint]
  have hkpow : ‖(k : ℂ) ^ (-afeCriticalPoint (-t))‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    apply Real.rpow_le_one_of_one_le_of_nonpos hkOne
    simp [afeCriticalPoint]
  unfold hughesYoungMollifierPairTerm
  simp only [norm_mul]
  calc
    ‖shortMobiusSquareCoeff T h‖ * ‖(h : ℂ) ^ (-afeCriticalPoint t)‖ *
          ‖shortMobiusSquareCoeff T k‖ *
          ‖(k : ℂ) ^ (-afeCriticalPoint (-t))‖ ≤
        ‖shortMobiusSquareCoeff T h‖ * 1 *
          ‖shortMobiusSquareCoeff T k‖ * 1 := by gcongr
    _ = _ := by ring

theorem aestronglyMeasurable_hughesYoungActiveWholeHighRemainder
    {q : ℕ} (hq : 0 < q) (a b R K : ℕ) :
    AEStronglyMeasurable (fun t : ℝ =>
      hughesYoungActiveWholeHighRemainder q a b R K t) := by
  let F : ℝ × ℝ → ℂ := fun z =>
    hughesYoungActiveHighPairRemainder q a b R K z.1 z.2
  have hF : AEMeasurable F := by
    unfold F hughesYoungActiveHighPairRemainder
    apply AEMeasurable.tsum
    intro p
    by_cases hp1 : p.1 = 0
    · have hz : (fun z : ℝ × ℝ =>
          ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
            hughesYoungRightPairTerm z.1 (2 * q) z.2 p) = 0 := by
        funext z
        rw [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero
          z.1 (2 * q) z.2 hp1]
        simp
      rw [hz]
      exact aemeasurable_const
    by_cases hp2 : p.2 = 0
    · have hz : (fun z : ℝ × ℝ =>
          ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
            hughesYoungRightPairTerm z.1 (2 * q) z.2 p) = 0 := by
        funext z
        rw [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero
          z.1 (2 * q) z.2 hp2]
        simp
      rw [hz]
      exact aemeasurable_const
    exact (continuous_const.mul
      (continuous_uncurry_hughesYoungRightPairTerm_height_ordinate
        (by exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hq)
        (Nat.pos_of_ne_zero hp1) (Nat.pos_of_ne_zero hp2))).aemeasurable
  unfold hughesYoungActiveWholeHighRemainder
  exact hF.aestronglyMeasurable.integral_prod_right'

noncomputable def hughesYoungActiveWholeTwistedIntegrand
    (T : ℝ) (R K : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveWholeSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t

noncomputable def hughesYoungActiveWholeTwistedRemainder
    (q : ℕ) (T : ℝ) (R K : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungActiveWholeHighRemainder q
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t

/-- The exact `ℓ¹` mass of the squared Möbius coefficients occurring in the
Hughes--Young source polynomial. -/
noncomputable def hughesYoungMollifierCoefficientMass (T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ‖shortMobiusSquareCoeff T h‖

theorem hughesYoungMollifierCoefficientMass_nonneg (T : ℝ) :
    0 ≤ hughesYoungMollifierCoefficientMass T := by
  unfold hughesYoungMollifierCoefficientMass
  positivity

/-- Uniform pointwise bound for the complete mollifier-weighted opening-line
remainder.  The coefficient dependence is retained exactly as an `ℓ¹` mass;
no cardinality proxy is inserted here. -/
theorem exists_norm_hughesYoungActiveWholeTwistedRemainder_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 0 < R →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ∀ t ∈ Set.Icc (T / 4) (4 * T),
        ‖hughesYoungActiveWholeTwistedRemainder q T R K t‖ ≤
          hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
            ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
              (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
              hughesYoungReferenceDivisorPairMass η) * L) := by
  classical
  obtain ⟨L, hL, hpair⟩ :=
    exists_norm_hughesYoungActiveWholeHighRemainder_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T R K hT hR hcover t ht
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  have hB0 : 0 ≤ B := by
    unfold B
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungReferenceDivisorPairMass_nonneg η)) hL.le
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscalar : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos hpi]
  unfold hughesYoungActiveWholeTwistedRemainder
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            hughesYoungActiveWholeHighRemainder q
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ ≤
        ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeHighRemainder q
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ‖hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeHighRemainder q
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ :=
      Finset.sum_le_sum fun h _hhmem => norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) * B := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
      have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
      have hmoll := norm_hughesYoungMollifierPairTerm_le T t hh hk
      have hrem : ‖hughesYoungActiveWholeHighRemainder q
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ ≤ B := by
        exact hpair
          (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) hR
          (hcover h hhmem k hkmem)
          hT1 ht
      simp only [norm_mul, hscalar]
      gcongr
    _ = (∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖) * ((1 / Real.pi) * B) := by
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _hhmem
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hkmem
      ring
    _ = hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) * B := by
      have hprod :
          (∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖) =
            hughesYoungMollifierCoefficientMass T ^ 2 := by
        unfold hughesYoungMollifierCoefficientMass
        symm
        rw [pow_two, Finset.sum_mul_sum]
      rw [hprod]
      ring
    _ = _ := by rfl

/-- Exact source-entry decomposition after the legal finite active contour
transfer.  The coverage premise only chooses enough dyadic scales to cover
every positive pair below the product cutoff. -/
theorem ofReal_twistedZetaMomentIntegrand_eq_active_add_remainder
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    (twistedZetaMomentIntegrand T t : ℂ) =
      hughesYoungActiveWholeTwistedIntegrand T R K t +
        hughesYoungActiveWholeTwistedRemainder q T R K t := by
  rw [ofReal_twistedZetaMomentIntegrand_eq_conjugate_product,
    shortMobiusPolynomial_sq_eq, shortMobiusPolynomial_sq_eq]
  unfold hughesYoungActiveWholeTwistedIntegrand
    hughesYoungActiveWholeTwistedRemainder
    hughesYoungMollifierPairTerm
  calc
    ((∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t)) *
        (∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t))) *
        riemannZeta (afeCriticalPoint t) ^ 2 *
        riemannZeta (afeCriticalPoint (-t)) ^ 2) =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t)) *
          (shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t))) *
          (riemannZeta (afeCriticalPoint t) ^ 2 *
            riemannZeta (afeCriticalPoint (-t)) ^ 2) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _hhmem
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hkmem
      ring
    _ = ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ((shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
              shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
              (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t) +
            (shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
              shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
              (1 / (Real.pi : ℂ)) *
              hughesYoungActiveWholeHighRemainder q
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
      apply Finset.sum_congr rfl
      intro h hhmem
      apply Finset.sum_congr rfl
      intro k hkmem
      have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
      have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
      have ha : 0 < hughesYoungReducedLeft h k :=
        hughesYoungReducedLeft_pos hh
      have hb : 0 < hughesYoungReducedRight h k :=
        hughesYoungReducedRight_pos hh hk
      have hzeta := hughesYoungZetaProduct_eq_activeWholeSmall_add_remainder
        hq ha hb hR (hcover h hhmem k hkmem) η hη0 hη hT ht
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hzetaDiv :
          riemannZeta (afeCriticalPoint t) ^ 2 *
              riemannZeta (afeCriticalPoint (-t)) ^ 2 =
            (1 / (Real.pi : ℂ)) *
              (hughesYoungActiveWholeSmall T
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t +
                hughesYoungActiveWholeHighRemainder q
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t) := by
        calc
          riemannZeta (afeCriticalPoint t) ^ 2 *
                riemannZeta (afeCriticalPoint (-t)) ^ 2 =
              (1 / (Real.pi : ℂ)) *
                ((Real.pi : ℂ) *
                  (riemannZeta (afeCriticalPoint t) ^ 2 *
                    riemannZeta (afeCriticalPoint (-t)) ^ 2)) := by
            field_simp [hpi]
          _ = _ := by rw [hzeta]
      rw [hzetaDiv]
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

noncomputable def hughesYoungActiveWholeSmoothedRemainder
    (q : ℕ) (T : ℝ) (R K : ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungActiveWholeTwistedRemainder q T R K t

noncomputable def hughesYoungActiveWholeSmoothedMoment
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungActiveWholeTwistedIntegrand T R K t

theorem integrable_weight_mul_mollifierPair_activeWholeRemainder
    {q R K h k : ℕ} (hq : 0 < q) (hR : 0 < R)
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hh : 0 < h) (hk : 0 < k)
    (hcover : (((hughesYoungReducedLeft h k) *
        (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
          hughesYoungActiveWholeHighRemainder q
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
  obtain ⟨L, hL, hremBound⟩ :=
    exists_norm_hughesYoungActiveWholeHighRemainder_le q hq η hη0 hη
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  let D : ℝ := ‖shortMobiusSquareCoeff T h‖ *
    ‖shortMobiusSquareCoeff T k‖ * (1 / Real.pi) * B
  let g : ℝ → ℝ := fun t => hughesYoungHeightWeight T t * D
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hB0 : 0 ≤ B := by
    unfold B
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungReferenceDivisorPairMass_nonneg η)) hL.le
  have hD0 : 0 ≤ D := by
    unfold D
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)) hB0
  have hcutoffCompact : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      hughesYoungCutoff.support
  have hweightCompact : HasCompactSupport (hughesYoungHeightWeight T) := by
    simpa only [hughesYoungHeightWeight] using
      hcutoffCompact.comp_smul (inv_ne_zero hT0.ne')
  have hg : Integrable g := by
    exact ((contDiff_hughesYoungHeightWeight T).continuous.mul
      (continuous_const : Continuous (fun _t : ℝ => D))).integrable_of_hasCompactSupport
        hweightCompact.mul_right
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
          hughesYoungActiveWholeHighRemainder q
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
    exact (Complex.continuous_ofReal.comp
      (contDiff_hughesYoungHeightWeight T).continuous).aestronglyMeasurable.mul
      (((continuous_hughesYoungMollifierPairTerm T hh hk).aestronglyMeasurable.mul
        aestronglyMeasurable_const).mul
        (aestronglyMeasurable_hughesYoungActiveWholeHighRemainder hq
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K))
  apply hg.mono' hmeas
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw, g]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    have hrem : ‖hughesYoungActiveWholeHighRemainder q
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ ≤ B := by
      exact hremBound
        (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) hR hcover
        (by linarith [Real.exp_one_gt_d9]) ht
    have hpair := norm_hughesYoungMollifierPairTerm_le T t hh hk
    have hw0 := hughesYoungHeightWeight_nonneg T t
    have hpi : 0 < Real.pi := Real.pi_pos
    unfold g D
    simp only [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
    have hscalar : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
      simp [Real.norm_eq_abs, abs_of_pos hpi]
    rw [hscalar]
    gcongr

theorem integrable_weight_mul_hughesYoungActiveWholeTwistedRemainder
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveWholeTwistedRemainder q T R K t) := by
  classical
  unfold hughesYoungActiveWholeTwistedRemainder
  have hfun : (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            hughesYoungActiveWholeHighRemainder q
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t) =
      (fun t : ℝ =>
        ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            (hughesYoungHeightWeight T t : ℂ) *
              (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
                hughesYoungActiveWholeHighRemainder q
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
    funext t
    simp_rw [Finset.mul_sum]
  rw [hfun]
  apply integrable_finsetSum
  intro h hhmem
  apply integrable_finsetSum
  intro k hkmem
  exact integrable_weight_mul_mollifierPair_activeWholeRemainder
    hq hR η hη0 hη hT
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1)
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1)
    (hcover h hhmem k hkmem)

theorem integrable_weight_mul_hughesYoungActiveWholeTwistedIntegrand
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveWholeTwistedIntegrand T R K t) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hactual : Integrable (fun t : ℝ =>
      ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ)) :=
    (integrable_hughesYoungSmoothedMoment_integrand hT0).ofReal
  have hrem := integrable_weight_mul_hughesYoungActiveWholeTwistedRemainder
    hq hR η hη0 hη hT hcover
  apply (hactual.sub hrem).congr
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    have hid := ofReal_twistedZetaMomentIntegrand_eq_active_add_remainder
      hq hR η hη0 hη hT ht hcover
    simp only [Pi.sub_apply, Complex.ofReal_mul]
    rw [hid]
    ring

/-- Exact height-integrated active/remainder decomposition.  Integrability
of both pieces is established independently before linearity is used. -/
theorem ofReal_hughesYoungSmoothedMoment_eq_active_add_remainder
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    (hughesYoungSmoothedMoment T : ℂ) =
      hughesYoungActiveWholeSmoothedMoment T R K +
        hughesYoungActiveWholeSmoothedRemainder q T R K := by
  have hactive :=
    integrable_weight_mul_hughesYoungActiveWholeTwistedIntegrand
      hq hR η hη0 hη hT hcover
  have hrem :=
    integrable_weight_mul_hughesYoungActiveWholeTwistedRemainder
      hq hR η hη0 hη hT hcover
  unfold hughesYoungSmoothedMoment hughesYoungActiveWholeSmoothedMoment
    hughesYoungActiveWholeSmoothedRemainder
  rw [← _root_.integral_complex_ofReal]
  rw [← integral_add hactive hrem]
  apply integral_congr_ae
  filter_upwards with t
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    have hid := ofReal_twistedZetaMomentIntegrand_eq_active_add_remainder
      hq hR η hη0 hη hT ht hcover
    push_cast
    rw [hid]
    ring

/-- Quantitative opening-line remainder after the physical height integral.
The factor `15T/4` is the exact length of the support interval
`[T/4,4T]`. -/
theorem exists_norm_hughesYoungActiveWholeSmoothedRemainder_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 0 < R →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ‖hughesYoungActiveWholeSmoothedRemainder q T R K‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
            ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
            (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
            hughesYoungReferenceDivisorPairMass η) * L) := by
  obtain ⟨L, hL, hpoint⟩ :=
    exists_norm_hughesYoungActiveWholeTwistedRemainder_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T R K hT hR hcover
  let A : ℝ :=
    hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
      ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
        ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
        (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        hughesYoungReferenceDivisorPairMass η) * L)
  let B : ℝ → ℝ :=
    Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA0 : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg
        (pow_nonneg (hughesYoungMollifierCoefficientMass_nonneg T) 2)
        (by positivity))
      (mul_nonneg
        (mul_nonneg (by positivity)
          (hughesYoungReferenceDivisorPairMass_nonneg η)) hL.le)
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  unfold hughesYoungActiveWholeSmoothedRemainder
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) =
        ∫ _t in Set.Icc (T / 4) (4 * T), A by
          exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, norm_zero]
      simpa only [B] using Set.indicator_nonneg (fun _ _ => hA0) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hrem := hpoint hT hR hcover t ht
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungActiveWholeTwistedRemainder q T R K t‖ ≤
          1 * ‖hughesYoungActiveWholeTwistedRemainder q T R K t‖ := by
            gcongr
        _ ≤ A := by simpa only [one_mul, A] using hrem

end RiemannZeta.GuthMaynard
