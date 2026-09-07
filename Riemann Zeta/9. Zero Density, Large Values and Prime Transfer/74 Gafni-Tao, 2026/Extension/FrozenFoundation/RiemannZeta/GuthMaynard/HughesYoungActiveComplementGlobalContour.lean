import RiemannZeta.GuthMaynard.HughesYoungActiveComplementWholeLine

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global finite-rectangle identity for the active complement

This file performs the first global assembly needed to remove the remaining
Hughes--Young product-truncation source.  It keeps the literal DFI signed
central series, the actual mollifier range, and the physical height integral.
No estimate is included in any definition.
-/

/-- The complete mollifier-weighted non-lower source on a finite segment of
the even opening line `Re w = 2Q`. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenOpeningFinite
    (Q : ℕ) (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K

/-- The two horizontal sides of the same finite contour rectangle, already
with the orientation factor that occurs in the solved rectangle identity. -/
noncomputable def hughesYoungNonLowerActiveComplementHorizontalCorrection
    (Q : ℕ) (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, (-I) *
        ((∫ s : ℝ in hughesYoungSmallContour T..(((2 * Q : ℕ) : ℝ)),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedSourceComplex
                T t ((s : ℂ) + (H : ℂ) * I)
                  h k (hughesYoungReducedLeft h k)
                    (hughesYoungReducedRight h k) R K) -
          (∫ s : ℝ in hughesYoungSmallContour T..(((2 * Q : ℕ) : ℝ)),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedSourceComplex
                T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                  h k (hughesYoungReducedLeft h k)
                    (hughesYoungReducedRight h k) R K))

/-- The pairwise finite-rectangle transfer kept under the physical-height
integral.  Keeping the subtraction inside the integral avoids assuming the
separate integrability of its two pieces before their quantitative majorants
have been established. -/
noncomputable def hughesYoungNonLowerActiveComplementFiniteRectangleTransfer
    (Q : ℕ) (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ,
        (∫ u in -H..H,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementSignedSourceComplex
              T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                h k (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K) -
          (-I) *
            ((∫ s : ℝ in hughesYoungSmallContour T..(((2 * Q : ℕ) : ℝ)),
                (hughesYoungHeightWeight T t : ℂ) *
                  hughesYoungNonLowerActiveComplementSignedSourceComplex
                    T t ((s : ℂ) + (H : ℂ) * I)
                      h k (hughesYoungReducedLeft h k)
                        (hughesYoungReducedRight h k) R K) -
              (∫ s : ℝ in hughesYoungSmallContour T..(((2 * Q : ℕ) : ℝ)),
                (hughesYoungHeightWeight T t : ℂ) *
                  hughesYoungNonLowerActiveComplementSignedSourceComplex
                    T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                      h k (hughesYoungReducedLeft h k)
                        (hughesYoungReducedRight h k) R K))

/-- Exact global finite-rectangle transfer at the native ordinate height.
The theorem consumes the literal source object and exposes exactly the two
quantitative obligations: the even opening line and the horizontal edges. -/
theorem hughesYoungNonLowerActiveComplementIntegratedCentralSource_eq_finiteRectangleTransfer
    {T : ℝ} (hT : Real.exp 4 ≤ T) {R K : ℕ} (hR : 0 < R)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        hughesYoungDyadicRatio *
            (((hughesYoungReducedLeft h k) *
              (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
          hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) :
    hughesYoungNonLowerActiveComplementIntegratedCentralSource T R K =
      hughesYoungNonLowerActiveComplementFiniteRectangleTransfer
        Q T (T / 8) R K := by
  classical
  have hT1 : 1 ≤ T := by
    have h14 : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h14.trans hT]
  have hT8 : 8 ≤ T := by
    have he2 : 3 < Real.exp 2 := by
      calc
        (3 : ℝ) = 2 + 1 := by norm_num
        _ < Real.exp 2 := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    have he4 : 8 < Real.exp 4 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      nlinarith
    linarith
  have hH : 1 ≤ T / 8 := by linarith
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  unfold hughesYoungNonLowerActiveComplementIntegratedCentralSource
    hughesYoungNonLowerActiveComplementFiniteRectangleTransfer
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  apply integral_congr_ae
  filter_upwards with t
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  have hrect :=
    intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_sub_eq_horizontal_even
      (T := T) hc.1 (hc.2.1.trans (by norm_num)) ha hb hR
        (hcover h hhmem k hkmem) hQ t hH h k
  have hsource :
      (∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K) =
      ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K := by
    apply intervalIntegral.integral_congr
    intro u _hu
    change
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K =
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K
    rw [hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_eq
      T t (hughesYoungSmallContour T) u hh hk]
  calc
    _ = ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((hughesYoungSmallContour T : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K := hsource.symm
    _ = _ := by
      apply (eq_sub_iff_add_eq).2
      have hsolve := (sub_eq_iff_eq_add.mp hrect).symm
      simpa [add_comm] using hsolve

end RiemannZeta.GuthMaynard
