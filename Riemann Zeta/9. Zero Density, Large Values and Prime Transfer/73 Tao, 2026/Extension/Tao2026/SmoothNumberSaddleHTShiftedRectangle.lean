import Tao2026.SmoothNumberSaddleHTShiftedRightLine
import GafniTao.SharpPerronResidues

/-!
# Exact shifted zeta rectangle for the HT transform

This module translates the frozen zeta-surrogate residue machinery to the
Hildebrand--Tenenbaum Perron integrand
`-zeta'(s+z)/zeta(s+z) * y^z/z`.  On a positive-real rectangle containing
`z=1-s`, a literal surrogate-zero-free hypothesis leaves exactly that pole,
with residue `y^(1-s)/(1-s)`.  The right vertical line is consequently the
source main term plus the two horizontal edges and the left vertical edge.

Quantitative zero-free-region and edge estimates are deliberately separate.
-/

open Complex Filter Set Topology Asymptotics
open scoped Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTShiftedZetaPerronIntegrand
    (y : ℝ) (s z : ℂ) : ℂ :=
  -(GafniTao.sharpPerronMonomial y z) *
      logDeriv GafniTao.sharpZetaSurrogate (s + z) +
    GafniTao.sharpPerronMonomial y z / (s + z - 1)

theorem smoothSaddleHTShiftedZetaPerronIntegrand_eq
    {y : ℝ} {s z : ℂ} (hz0 : z ≠ 0) (hsz1 : s + z ≠ 1)
    (hzeta : riemannZeta (s + z) ≠ 0) :
    smoothSaddleHTShiftedZetaPerronIntegrand y s z =
      -(logDeriv riemannZeta (s + z)) * ((y : ℂ) ^ z / z) := by
  rw [smoothSaddleHTShiftedZetaPerronIntegrand,
    GafniTao.logDeriv_sharpZetaSurrogate_eq hsz1 hzeta]
  unfold GafniTao.sharpPerronMonomial
  field_simp [hz0, sub_ne_zero.mpr hsz1]
  ring

theorem smoothSaddleHTShiftedZetaPerronIntegrand_near_pole
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs1 : s ≠ 1) :
    (smoothSaddleHTShiftedZetaPerronIntegrand y s - fun z =>
        GafniTao.sharpPerronMonomial y (1 - s) / (z - (1 - s)))
      =O[𝓝[≠] (1 - s)] (1 : ℂ → ℂ) := by
  let p : ℂ := 1 - s
  have hp0 : p ≠ 0 := by
    dsimp [p]
    exact sub_ne_zero.mpr (Ne.symm hs1)
  have hmono : DifferentiableAt ℂ (GafniTao.sharpPerronMonomial y) p :=
    GafniTao.differentiableAt_sharpPerronMonomial hy hp0
  have hsur : GafniTao.sharpZetaSurrogate (s + p) ≠ 0 := by
    have hsp : s + p = 1 := by dsimp [p]; ring
    rw [hsp, GafniTao.sharpZetaSurrogate_one]
    norm_num
  have hlog : DifferentiableAt ℂ
      (fun z => logDeriv GafniTao.sharpZetaSurrogate (s + z)) p :=
    (GafniTao.differentiableAt_logDeriv_sharpZetaSurrogate hsur).comp p
      (differentiableAt_const (c := s) |>.add differentiableAt_id)
  have hfirstDiff : DifferentiableAt ℂ
      (fun z => -(GafniTao.sharpPerronMonomial y z) *
        logDeriv GafniTao.sharpZetaSurrogate (s + z)) p :=
    hmono.neg.mul hlog
  have hfirst :
      (fun z => -(GafniTao.sharpPerronMonomial y z) *
          logDeriv GafniTao.sharpZetaSurrogate (s + z))
        =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hfirstDiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hprincipal :
      ((fun z : ℂ => 1 / (z - p)) - fun z => (1 : ℂ) / (z - p))
        =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    simpa using (isBigO_zero (1 : ℂ → ℂ) (𝓝[≠] p))
  have hcorr := GafniTao.mul_sub_principal_isBigO_one hprincipal hmono
  have hsum := hfirst.add hcorr
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards with z
  simp only [smoothSaddleHTShiftedZetaPerronIntegrand, Pi.sub_apply]
  have hden : s + z - 1 = z - p := by dsimp [p]; ring
  rw [hden]
  ring

private theorem smoothSaddleHTShiftedZetaPerronIntegrand_holomorphicOn_rectangle_diff
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : 0 < left) (hlr : left < right)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    HolomorphicOn (smoothSaddleHTShiftedZetaPerronIntegrand y s)
      (Rectangle
          ((left : ℂ) - (T : ℂ) * Complex.I)
          ((right : ℂ) + (T : ℂ) * Complex.I) \ {1 - s}) := by
  intro z hz
  have hzRect := hz.1
  have hzRe := hzRect.1
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_re] at hzRe
  have hzRe' : z.re ∈ Set.uIcc left right := by simpa using hzRe
  rw [Set.uIcc_of_le hlr.le] at hzRe'
  have hz0 : z ≠ 0 := by
    intro hzZero
    subst z
    simp at hzRe'
    linarith
  have hmono := GafniTao.differentiableAt_sharpPerronMonomial hy hz0
  have hlog : DifferentiableAt ℂ
      (fun w => logDeriv GafniTao.sharpZetaSurrogate (s + w)) z :=
    (GafniTao.differentiableAt_logDeriv_sharpZetaSurrogate
      (hsur z hzRect)).comp z
        (differentiableAt_const (c := s) |>.add differentiableAt_id)
  have hden : s + z - 1 ≠ 0 := by
    intro h
    apply hz.2
    simp only [Set.mem_singleton_iff]
    linear_combination h
  exact ((hmono.neg.mul hlog).add
    (hmono.div
      ((differentiableAt_const (c := s)).add differentiableAt_id |>.sub_const 1)
      hden)).differentiableWithinAt

theorem smoothSaddleHTShiftedZetaPerron_rectangleIntegral_eq_main
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : 0 < left) (hleftPole : left < (1 - s).re)
    (hpoleRight : (1 - s).re < right) (hpoleBottom : -T < (1 - s).im)
    (hpoleTop : (1 - s).im < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    RectangleIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I) =
      GafniTao.sharpPerronMonomial y (1 - s) := by
  have hlr : left < right := hleftPole.trans hpoleRight
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    simp at hleftPole
    linarith
  apply ResidueTheoremOnRectangleWithSimplePole'
      (p := 1 - s) (A := GafniTao.sharpPerronMonomial y (1 - s))
  · simp
    exact hlr.le
  · simp
    linarith
  · rw [rectangle_mem_nhds_iff, mem_reProdIm]
    have hreLeft :
        ((left : ℂ) - (T : ℂ) * Complex.I).re = left := by simp
    have hreRight :
        ((right : ℂ) + (T : ℂ) * Complex.I).re = right := by simp
    have himLeft :
        ((left : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
    have himRight :
        ((right : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
    rw [hreLeft, hreRight, himLeft, himRight]
    constructor
    · change (1 - s).re ∈ Set.uIoo left right
      rw [Set.uIoo_of_le hlr.le]
      exact ⟨hleftPole, hpoleRight⟩
    · change (1 - s).im ∈ Set.uIoo (-T) T
      rw [Set.uIoo_of_le (by linarith : -T ≤ T)]
      exact ⟨hpoleBottom, hpoleTop⟩
  · exact smoothSaddleHTShiftedZetaPerronIntegrand_holomorphicOn_rectangle_diff
      hy hleft hlr hsur
  · exact smoothSaddleHTShiftedZetaPerronIntegrand_near_pole hy hs1

theorem smoothSaddleHTShiftedZetaPerron_rightEdge_eq_main_add_edges
    {y left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : 0 < left) (hleftPole : left < (1 - s).re)
    (hpoleRight : (1 - s).re < right) (hpoleBottom : -T < (1 - s).im)
    (hpoleTop : (1 - s).im < T)
    (hsur : ∀ z ∈ Rectangle
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I),
      GafniTao.sharpZetaSurrogate (s + z) ≠ 0) :
    VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s) right (-T) T =
      GafniTao.sharpPerronMonomial y (1 - s) -
          HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left right (-T) +
        HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left right T +
          VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
            left (-T) T := by
  have hrect := smoothSaddleHTShiftedZetaPerron_rectangleIntegral_eq_main
    hy hleft hleftPole hpoleRight hpoleBottom hpoleTop hsur
  have hreLeft :
      ((left : ℂ) - (T : ℂ) * Complex.I).re = left := by simp
  have hreRight :
      ((right : ℂ) + (T : ℂ) * Complex.I).re = right := by simp
  have himLeft :
      ((left : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
  have himRight :
      ((right : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

theorem smoothSaddleHTSharpPerronMonomial_one_sub_eq_sourceMainTerm
    (y : ℕ) (s : ℂ) :
    GafniTao.sharpPerronMonomial (y : ℝ) (1 - s) =
      smoothSaddleHTSourceMainTerm y s := by
  unfold GafniTao.sharpPerronMonomial smoothSaddleHTSourceMainTerm
  have hyCast : (y : ℂ) = (((y : ℝ) : ℂ)) := by norm_num
  rw [hyCast]

theorem smoothSaddleHTShiftedZetaPerron_rightLine_eq_VIntegral'
    {y right T : ℝ} {s : ℂ} (hright : 0 < right)
    (hpoleRight : (1 - s).re < right)
    (hsur : ∀ u ∈ Set.uIcc (-T) T,
      GafniTao.sharpZetaSurrogate
        (s + ((right : ℂ) + (u : ℂ) * Complex.I)) ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ u in (-T)..T,
          (-deriv riemannZeta
                (s + ((right : ℂ) + (u : ℂ) * Complex.I)) /
              riemannZeta
                (s + ((right : ℂ) + (u : ℂ) * Complex.I))) *
            (y : ℂ) ^ ((right : ℂ) + (u : ℂ) * Complex.I) /
              ((right : ℂ) + (u : ℂ) * Complex.I)) =
      VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand y s)
        right (-T) T := by
  rw [VIntegral']
  simp only [VIntegral, smul_eq_mul]
  have hscalar :
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
        1 / (2 * (Real.pi : ℂ)) := by
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [← mul_assoc, hscalar]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hz0 : (right : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hsz1 :
      s + ((right : ℂ) + (u : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hpole : 1 - s = (right : ℂ) + (u : ℂ) * Complex.I := by
      rw [← h]
      ring
    have hre := congrArg Complex.re hpole
    have hre' : (1 - s).re = right := by simpa using hre
    exact (ne_of_lt hpoleRight) hre'
  have hzeta : riemannZeta
      (s + ((right : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 := by
    intro hzeta
    apply hsur u hu
    exact (GafniTao.sharpZetaSurrogate_eq_zero_iff hsz1).2 hzeta
  dsimp only
  rw [smoothSaddleHTShiftedZetaPerronIntegrand_eq hz0 hsz1 hzeta]
  simp only [logDeriv_apply]
  ring

theorem smoothSaddleHTShiftedPerron_rightLine_eq_main_add_edges
    {y : ℕ} {left right T : ℝ} {s : ℂ}
    (hy : 0 < y) (hleft : 0 < left) (hleftPole : left < (1 - s).re)
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
      smoothSaddleHTSourceMainTerm y s -
          HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left right (-T) +
        HIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left right T +
          VIntegral' (smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ) s)
            left (-T) T := by
  have hright : 0 < right :=
    hleft.trans (hleftPole.trans hpoleRight)
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
    · have hlr : left ≤ right := (hleftPole.trans hpoleRight).le
      simpa [Set.uIcc_of_le hlr] using
        (show right ∈ Set.Icc left right from ⟨hlr, le_rfl⟩)
    · have hT : -T ≤ T := by
        exact (hpoleBottom.trans hpoleTop).le
      simpa [Set.uIcc_of_le hT] using hu
  have hyCast : (y : ℂ) = (((y : ℝ) : ℂ)) := by norm_num
  rw [hyCast]
  rw [smoothSaddleHTShiftedZetaPerron_rightLine_eq_VIntegral'
    (y := (y : ℝ)) hright hpoleRight hsurRight]
  rw [smoothSaddleHTShiftedZetaPerron_rightEdge_eq_main_add_edges
    (y := (y : ℝ)) (s := s) (left := left) (right := right) (T := T)
    (by positivity) hleft hleftPole hpoleRight hpoleBottom hpoleTop hsur]
  rw [smoothSaddleHTSharpPerronMonomial_one_sub_eq_sourceMainTerm y s]

theorem smoothSaddleHTSource_shiftedPerron_rightLine_eq_main_add_edges
    {y : ℕ} {left right T beta t : ℝ}
    (hy : 0 < y) (hleft : 0 < left) (hleftBeta : left < beta)
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
  apply smoothSaddleHTShiftedPerron_rightLine_eq_main_add_edges
    hy hleft
  · simpa using hleftBeta
  · simpa using hbetaRight
  · rw [abs_lt] at ht
    simp
    linarith
  · rw [abs_lt] at ht
    simp
    linarith
  · exact hsur

end

end Tao2026
