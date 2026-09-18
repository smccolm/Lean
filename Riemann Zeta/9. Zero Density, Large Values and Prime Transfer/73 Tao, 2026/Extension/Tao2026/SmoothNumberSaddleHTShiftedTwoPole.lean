import Tao2026.SmoothNumberSaddleHTContourParameters
import GafniTao.SharpPerronResidue

/-!
# The two-pole shifted Perron rectangle

When the Perron contour is moved past the origin, the shifted zeta integrand
has two enclosed poles: the physical zeta pole at `z = 1 - s` and the Perron
kernel pole at `z = 0`.  This module computes the second residue and proves the
exact finite-height rectangle identity with both terms.  It is the cancellation
identity needed in the small-`beta` branch of Hildebrand--Tenenbaum Lemma 6.
-/

open Complex Filter Set Topology Asymptotics
open scoped Interval

namespace Tao2026

noncomputable section

/-- The exact coefficient at the Perron-kernel pole `z = 0`, kept in the
entire-surrogate coordinates used by the contour proof. -/
noncomputable def smoothSaddleHTShiftedOriginResidue (s : ℂ) : ℂ :=
  -logDeriv GafniTao.sharpZetaSurrogate s + 1 / (s - 1)

/-- At every regular physical point, the origin coefficient is the classical
negative zeta logarithmic derivative. -/
theorem smoothSaddleHTShiftedOriginResidue_eq
    {s : ℂ} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    smoothSaddleHTShiftedOriginResidue s =
      -logDeriv riemannZeta s := by
  rw [smoothSaddleHTShiftedOriginResidue,
    GafniTao.logDeriv_sharpZetaSurrogate_eq hs1 hzeta]
  ring

/-- Local principal part of the shifted integrand at the Perron-kernel pole. -/
theorem smoothSaddleHTShiftedZetaPerronIntegrand_near_origin
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs1 : s ≠ 1)
    (hsur : GafniTao.sharpZetaSurrogate s ≠ 0) :
    (smoothSaddleHTShiftedZetaPerronIntegrand y s - fun z =>
        smoothSaddleHTShiftedOriginResidue s / (z - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  let g : ℂ → ℂ := fun z =>
    -logDeriv GafniTao.sharpZetaSurrogate (s + z) +
      1 / (s + z - 1)
  have hmono :
      (GafniTao.sharpPerronMonomial y - fun z : ℂ => 1 / (z - 0))
        =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    simpa [GafniTao.sharpPerronMonomial] using
      GafniTao.sharpPerronMonomial_near_zero hy
  have hlog0 : DifferentiableAt ℂ
      (fun z => logDeriv GafniTao.sharpZetaSurrogate (s + z)) 0 :=
    (GafniTao.differentiableAt_logDeriv_sharpZetaSurrogate
      (by simpa using hsur)).comp 0
        ((differentiableAt_const (c := s)).add differentiableAt_id)
  have hlog : DifferentiableAt ℂ
      (fun z => -logDeriv GafniTao.sharpZetaSurrogate (s + z)) 0 :=
    hlog0.neg
  have hden : s + (0 : ℂ) - 1 ≠ 0 := by
    simpa using sub_ne_zero.mpr hs1
  have hrat : DifferentiableAt ℂ (fun z : ℂ => 1 / (s + z - 1)) 0 :=
    (differentiableAt_const (c := (1 : ℂ))).div
      (((differentiableAt_const (c := s)).add differentiableAt_id).sub_const 1)
      hden
  have hg : DifferentiableAt ℂ g 0 := hlog.add hrat
  have hlocal := GafniTao.mul_sub_principal_isBigO_one hmono hg
  refine hlocal.congr' ?_ ?_
  · filter_upwards with z
    simp only [smoothSaddleHTShiftedZetaPerronIntegrand, Pi.sub_apply]
    simp only [g, smoothSaddleHTShiftedOriginResidue, add_zero, one_mul]
    ring
  · filter_upwards with z
    simp

/-- Away from the origin and the translated zeta pole, the shifted integrand
is holomorphic on any surrogate-zero-free rectangle. -/
theorem smoothSaddleHTShiftedZetaPerronIntegrand_holomorphicOn_twoPoleDiff
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    HolomorphicOn (smoothSaddleHTShiftedZetaPerronIntegrand y s)
      (Rectangle
          ((left : ℂ) - (T : ℂ) * Complex.I)
          ((right : ℂ) + (T : ℂ) * Complex.I) \
        (({0, 1 - s} : Finset ℂ) : Set ℂ)) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hz.2
    simp [h]
  have hzp : z ≠ 1 - s := by
    intro h
    apply hz.2
    simp [h]
  have hmono := GafniTao.differentiableAt_sharpPerronMonomial hy hz0
  have hlog : DifferentiableAt ℂ
      (fun w => logDeriv GafniTao.sharpZetaSurrogate (s + w)) z :=
    (GafniTao.differentiableAt_logDeriv_sharpZetaSurrogate
      (hsur z hz.1)).comp z
        ((differentiableAt_const (c := s)).add differentiableAt_id)
  have hden : s + z - 1 ≠ 0 := by
    intro h
    apply hzp
    linear_combination h
  exact ((hmono.neg.mul hlog).add
    (hmono.div
      (((differentiableAt_const (c := s)).add differentiableAt_id).sub_const 1)
      hden)).differentiableWithinAt

/-- A negative-left shifted rectangle encloses exactly the Perron origin and
the physical zeta pole, provided the translated surrogate is zero-free. -/
theorem smoothSaddleHTShiftedZetaPerron_rectangleIntegral_eq_origin_add_main
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : left < 0) (hright : 0 < right) (hT : 0 < T)
    (hs1 : s ≠ 1) (hleftPole : left < (1 - s).re)
    (hpoleRight : (1 - s).re < right) (hpoleBottom : -T < (1 - s).im)
    (hpoleTop : (1 - s).im < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    RectangleIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I) =
      smoothSaddleHTShiftedOriginResidue s +
        GafniTao.sharpPerronMonomial y (1 - s) := by
  let S : Finset ℂ := {0, 1 - s}
  let A : ℂ → ℂ := fun p =>
    if p = 0 then smoothSaddleHTShiftedOriginResidue s
    else GafniTao.sharpPerronMonomial y (1 - s)
  have hp0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h0p : (0 : ℂ) ≠ 1 - s := Ne.symm hp0
  have hlr : left ≤ right := (hleft.trans hright).le
  have him : -T ≤ T := by linarith
  have hreRect :
      ((left : ℂ) - (T : ℂ) * Complex.I).re ≤
        ((right : ℂ) + (T : ℂ) * Complex.I).re := by
    simpa using hlr
  have himRect :
      ((left : ℂ) - (T : ℂ) * Complex.I).im ≤
        ((right : ℂ) + (T : ℂ) * Complex.I).im := by
    simpa using him
  have hsum : (∑ p ∈ S, A p) =
      smoothSaddleHTShiftedOriginResidue s +
        GafniTao.sharpPerronMonomial y (1 - s) := by
    simp [S, A, h0p, hp0]
  rw [← hsum]
  apply GafniTao.residueTheorem_finset hreRect himRect S A
  · intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · rw [rectangle_mem_nhds_iff, mem_reProdIm]
      constructor
      · simpa [Set.uIoo_of_le hlr] using
          (show (0 : ℝ) ∈ Set.Ioo left right from ⟨hleft, hright⟩)
      · simpa [Set.uIoo_of_le him] using
          (show (0 : ℝ) ∈ Set.Ioo (-T) T from ⟨by linarith, hT⟩)
    · rw [rectangle_mem_nhds_iff, mem_reProdIm]
      constructor
      · simpa [Set.uIoo_of_le hlr] using
          (show (1 - s).re ∈ Set.Ioo left right from
            ⟨hleftPole, hpoleRight⟩)
      · simpa [Set.uIoo_of_le him] using
          (show (1 - s).im ∈ Set.Ioo (-T) T from
            ⟨hpoleBottom, hpoleTop⟩)
  · simpa [S] using
      smoothSaddleHTShiftedZetaPerronIntegrand_holomorphicOn_twoPoleDiff
        hy hsur
  · intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · have hzeroRect : (0 : ℂ) ∈ Rectangle
          ((left : ℂ) - (T : ℂ) * Complex.I)
          ((right : ℂ) + (T : ℂ) * Complex.I) := by
        rw [Rectangle, mem_reProdIm]
        constructor <;> simp [Set.uIcc_of_le, hlr, him, hleft.le, hright.le,
          hT.le]
      simpa [A] using
        smoothSaddleHTShiftedZetaPerronIntegrand_near_origin hy hs1
          (by simpa using hsur 0 hzeroRect)
    · simpa [A, hp0] using
        smoothSaddleHTShiftedZetaPerronIntegrand_near_pole hy hs1

/-- Solving the two-pole rectangle identity for its right vertical edge. -/
theorem smoothSaddleHTShiftedZetaPerron_rightEdge_eq_origin_add_main_add_edges
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : left < 0) (hright : 0 < right) (hT : 0 < T)
    (hs1 : s ≠ 1) (hleftPole : left < (1 - s).re)
    (hpoleRight : (1 - s).re < right) (hpoleBottom : -T < (1 - s).im)
    (hpoleTop : (1 - s).im < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s) right (-T) T =
      smoothSaddleHTShiftedOriginResidue s +
        GafniTao.sharpPerronMonomial y (1 - s) -
          HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left right (-T) +
        HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left right T +
          VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left (-T) T := by
  have hrect :=
    smoothSaddleHTShiftedZetaPerron_rectangleIntegral_eq_origin_add_main
      hy hleft hright hT hs1 hleftPole hpoleRight hpoleBottom hpoleTop hsur
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  have hreLeft :
      ((left : ℂ) - (T : ℂ) * Complex.I).re = left := by simp
  have hreRight :
      ((right : ℂ) + (T : ℂ) * Complex.I).re = right := by simp
  have himLeft : ((left : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
  have himRight : ((right : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

/-- The analytic right line equals the two residues plus the three remaining
oriented edges. -/
theorem smoothSaddleHTShiftedPerron_rightLine_eq_origin_add_main_add_edges
    {y : ℕ} {left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : left < 0) (hright : 0 < right) (hT : 0 < T)
    (hs1 : s ≠ 1) (hleftPole : left < (1 - s).re)
    (hpoleRight : (1 - s).re < right) (hpoleBottom : -T < (1 - s).im)
    (hpoleTop : (1 - s).im < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (s + ((right : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (s + ((right : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((right : ℂ) + (u : ℂ) * Complex.I) /
                ((right : ℂ) + (u : ℂ) * Complex.I)) =
      smoothSaddleHTShiftedOriginResidue s +
        smoothSaddleHTSourceMainTerm y s -
          HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left right (-T) +
        HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left right T +
          VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left (-T) T := by
  have hlr : left ≤ right := (hleft.trans hright).le
  have him : -T ≤ T := by linarith
  have hsurRight : ∀ u ∈ Set.uIcc (-T) T,
      GafniTao.sharpZetaSurrogate
        (s + ((right : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 := by
    intro u hu
    apply hsur ((right : ℂ) + (u : ℂ) * Complex.I)
    change
      ((right : ℂ) + (u : ℂ) * Complex.I).re ∈
          Set.uIcc
            (((left : ℂ) - (T : ℂ) * Complex.I).re)
            (((right : ℂ) + (T : ℂ) * Complex.I).re) ∧
        ((right : ℂ) + (u : ℂ) * Complex.I).im ∈
          Set.uIcc
            (((left : ℂ) - (T : ℂ) * Complex.I).im)
            (((right : ℂ) + (T : ℂ) * Complex.I).im)
    constructor
    · simpa [Set.uIcc_of_le hlr] using
        (show right ∈ Set.Icc left right from ⟨hlr, le_rfl⟩)
    · simpa [Set.uIcc_of_le him] using hu
  have hyCast : (y : ℂ) = (((y : ℝ) : ℂ)) := by norm_num
  rw [hyCast]
  rw [smoothSaddleHTShiftedZetaPerron_rightLine_eq_VIntegral'
    (y := (y : ℝ)) hright hpoleRight hsurRight]
  rw [smoothSaddleHTShiftedZetaPerron_rightEdge_eq_origin_add_main_add_edges
    (y := (y : ℝ)) (s := s) (left := left) (right := right) (T := T)
    (by positivity) hleft hright hT hs1 hleftPole hpoleRight hpoleBottom
      hpoleTop hsur]
  rw [smoothSaddleHTSharpPerronMonomial_one_sub_eq_sourceMainTerm y s]

/-- Source-coordinate specialization of the two-pole right-line identity.
For `beta > 0`, every negative left edge lies to the left of both enclosed
poles. -/
theorem smoothSaddleHTSource_shiftedPerron_rightLine_eq_origin_add_main_add_edges
    {y : ℕ} {left right T beta t : ℝ}
    (hy : 0 < y) (hleft : left < 0) (hbeta : 0 < beta)
    (hbetaRight : beta < right) (ht : |t| < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((right : ℂ) + (u : ℂ) * Complex.I) /
                ((right : ℂ) + (u : ℂ) * Complex.I)) =
      smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSourceMainTerm y
          (smoothSaddleHTSourceExponent beta t) -
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left right (-T) +
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left right T +
        VIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left (-T) T := by
  have hright : 0 < right := hbeta.trans hbetaRight
  have hT : 0 < T := (abs_nonneg t).trans_lt ht
  have hs1 : smoothSaddleHTSourceExponent beta t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [smoothSaddleHTSourceExponent] at hre
    linarith
  apply smoothSaddleHTShiftedPerron_rightLine_eq_origin_add_main_add_edges
    hy hleft hright hT hs1
  · simpa using hleft.trans hbeta
  · simpa using hbetaRight
  · rw [abs_lt] at ht
    simp
    linarith
  · rw [abs_lt] at ht
    simp
    linarith
  · exact hsur

/-- Vinogradov--Korobov zero-freeness on an arbitrary translated rectangle.
The physical depth of its left side is exactly `beta - left`; this form is
needed when `left < 0` and both Perron poles are enclosed. -/
theorem smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK_left
    {c H left beta t T right : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hdepthOne : beta - left ≤ 1) (hleftRight : left ≤ right)
    (hT : 0 ≤ T) (hHeight : H ≤ |t| + T)
    (hWidth : beta - left ≤ c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate
        (smoothSaddleHTSourceExponent beta t + z) ≠ 0 := by
  intro z hz hsur
  let w : ℂ := smoothSaddleHTSourceExponent beta t + z
  have hzRe : z.re ∈ Set.Icc left right := by
    have : z.re ∈ Set.uIcc left right := by simpa using hz.1
    simpa [Set.uIcc_of_le hleftRight] using this
  have hTorder : -T ≤ T := by linarith
  have hzIm : z.im ∈ Set.Icc (-T) T := by
    have : z.im ∈ Set.uIcc (-T) T := by simpa using hz.2
    simpa [Set.uIcc_of_le hTorder] using this
  have hwReLower : 1 - (beta - left) ≤ w.re := by
    dsimp [w]
    simp [smoothSaddleHTSourceExponent]
    linarith [hzRe.1]
  have hwIm : w.im = t + z.im := by
    dsimp [w]
    simp [smoothSaddleHTSourceExponent]
  have hwAbsIm : |w.im| ≤ |t| + T := by
    rw [hwIm]
    calc
      |t + z.im| ≤ |t| + |z.im| := abs_add_le _ _
      _ ≤ |t| + T := by gcongr; exact abs_le.mpr hzIm
  have hsurW : GafniTao.sharpZetaSurrogate w = 0 := by
    simpa [w] using hsur
  by_cases hw1 : w = 1
  · rw [hw1, GafniTao.sharpZetaSurrogate_one] at hsurW
    exact one_ne_zero hsurW
  · have hzeta : riemannZeta w = 0 :=
      (GafniTao.sharpZetaSurrogate_eq_zero_iff hw1).mp hsurW
    by_cases hwOne : 1 ≤ w.re
    · exact (riemannZeta_ne_zero_of_one_le_re hwOne) hzeta
    · have hwReUpper : w.re ≤ 1 := (lt_of_not_ge hwOne).le
      have hwReZero : 0 ≤ w.re := by linarith
      have hwZeroSet : w ∈ GafniTao.zeroSet 0 (|t| + T) := by
        change w ∈ RiemannZeta.GuthMaynard.zerosInRect
          0 1 (-(|t| + T)) (|t| + T)
        rw [RiemannZeta.GuthMaynard.zerosInRect,
          Set.Finite.mem_toFinset, Set.mem_inter_iff]
        refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
          0 1 (-(|t| + T)) (|t| + T) w).mpr ?_, hzeta⟩
        exact ⟨hwReZero, hwReUpper, (abs_le.mp hwAbsIm).1,
          (abs_le.mp hwAbsIm).2⟩
      have hZeroRight := (hZeroFree hHeight).2.2 hwZeroSet
      linarith

/-- The two-pole source identity with its zero-free premise discharged by the
native rectangle-uniform Vinogradov--Korobov region. -/
theorem smoothSaddleHTSource_shiftedPerron_rightLine_eq_origin_add_main_add_edges_of_vK
    {c H left beta t T right : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 0 < y) (hleft : left < 0) (hbeta : 0 < beta)
    (hbetaRight : beta < right) (ht : |t| < T)
    (hdepthOne : beta - left ≤ 1) (hHeight : H ≤ |t| + T)
    (hWidth : beta - left ≤ c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((right : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((right : ℂ) + (u : ℂ) * Complex.I) /
                ((right : ℂ) + (u : ℂ) * Complex.I)) =
      smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSourceMainTerm y
          (smoothSaddleHTSourceExponent beta t) -
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left right (-T) +
        HIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left right T +
        VIntegral'
            (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
              (smoothSaddleHTSourceExponent beta t)) left (-T) T := by
  apply smoothSaddleHTSource_shiftedPerron_rightLine_eq_origin_add_main_add_edges
    hy hleft hbeta hbetaRight ht
  apply smoothSaddleHTSource_shiftedSurrogate_ne_zero_on_rectangle_of_vK_left
    hZeroFree hdepthOne
  · exact (hleft.trans (hbeta.trans hbetaRight)).le
  · exact (abs_nonneg t).trans_lt ht |>.le
  · exact hHeight
  · exact hWidth

/-- The three oriented edges of the negative-left small-`beta` contour. -/
noncomputable def smoothSaddleHTSmallBetaContourEdgeContribution
    (y : ℕ) (beta ε t : ℝ) : ℂ :=
  -HIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (-smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)
      (-smoothSaddleHTContourHeight y ε) +
    HIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (-smoothSaddleHTContourShift y ε)
      (smoothSaddleHTContourRight y beta)
      (smoothSaddleHTContourHeight y ε) +
    VIntegral'
      (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
        (smoothSaddleHTSourceExponent beta t))
      (-smoothSaddleHTContourShift y ε)
      (-smoothSaddleHTContourHeight y ε)
      (smoothSaddleHTContourHeight y ε)

/-- Exact small-`beta` decomposition.  In contrast to the positive-left
branch, the origin residue is present and is the term that cancels the
otherwise false scalar estimate near `beta = 0`. -/
theorem smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_smallBetaContourErrors
    {c H beta ε t : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 2 ≤ y) (hbeta : 0 < beta)
    (hdepthOne : beta + smoothSaddleHTContourShift y ε ≤ 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHeight : H ≤ |t| + smoothSaddleHTContourHeight y ε)
    (hWidth : beta + smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y ε)) :
    smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t =
      smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t -
          smoothSaddleHTContourTruncationError y beta ε t := by
  have hyPos : 0 < y := by omega
  have hshiftPos := smoothSaddleHTContourShift_pos hy ε
  have hright := smoothSaddleHTContourRight_gt hy beta
  have htStrict : |t| < smoothSaddleHTContourHeight y ε :=
    ht.trans_lt (smoothSaddleHTFrequencyCeiling_lt_contourHeight y ε)
  have hrect :=
    smoothSaddleHTSource_shiftedPerron_rightLine_eq_origin_add_main_add_edges_of_vK
      (c := c) (H := H)
      (left := -smoothSaddleHTContourShift y ε)
      (beta := beta) (t := t)
      (T := smoothSaddleHTContourHeight y ε)
      (right := smoothSaddleHTContourRight y beta)
      (y := y) hZeroFree hyPos (by linarith) hbeta hright htStrict
      (by simpa using hdepthOne) hHeight (by simpa using hWidth)
  have herr := smoothSaddleHTSource_shiftedPerron_error_identity
    (c := smoothSaddleHTContourRight y beta)
    (T := smoothSaddleHTContourHeight y ε)
    (y := y) (beta := beta) (t := t)
    hright (hbeta.trans hright) (by omega : 1 ≤ y)
  rw [smoothSaddleHTMangoldtMainTerm_eq_sourceMainTerm hyPos beta t]
  unfold smoothSaddleHTSmallBetaContourEdgeContribution
    smoothSaddleHTContourTruncationError
  linear_combination hrect - herr

/-- Norm form of the exact small-`beta` decomposition. -/
theorem norm_smoothSaddleHTMangoldtTransform_sub_mainTerm_le_smallBetaContourErrors
    {c H beta ε t : ℝ} {y : ℕ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hy : 2 ≤ y) (hbeta : 0 < beta)
    (hdepthOne : beta + smoothSaddleHTContourShift y ε ≤ 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε)
    (hHeight : H ≤ |t| + smoothSaddleHTContourHeight y ε)
    (hWidth : beta + smoothSaddleHTContourShift y ε ≤ c /
      GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y ε)) :
    ‖smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ +
        ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ +
          ‖smoothSaddleHTContourTruncationError y beta ε t‖ := by
  rw [smoothSaddleHTMangoldtTransform_sub_mainTerm_eq_smallBetaContourErrors
    hZeroFree hy hbeta hdepthOne ht hHeight hWidth]
  calc
    ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t -
          smoothSaddleHTContourTruncationError y beta ε t‖ ≤
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t) +
        smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖ +
          ‖smoothSaddleHTContourTruncationError y beta ε t‖ := norm_sub_le _ _
    _ ≤ (‖smoothSaddleHTShiftedOriginResidue
            (smoothSaddleHTSourceExponent beta t)‖ +
          ‖smoothSaddleHTSmallBetaContourEdgeContribution y beta ε t‖) +
          ‖smoothSaddleHTContourTruncationError y beta ε t‖ :=
      add_le_add (norm_add_le _ _) le_rfl

end

end Tao2026
