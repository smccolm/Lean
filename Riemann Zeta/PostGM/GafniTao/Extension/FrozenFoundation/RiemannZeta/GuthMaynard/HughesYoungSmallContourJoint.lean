import RiemannZeta.GuthMaynard.HughesYoungNativeCentralAssembly

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem continuous_uncurry_hughesYoungReducedMellinStaticComplex_vertical
    (T c : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungReducedMellinStaticComplex T z.1 h k
        ((c : ℂ) + (z.2 : ℂ) * I)) := by
  have hmoll : Continuous (fun z : ℝ × ℝ =>
      hughesYoungMollifierPairTerm T z.1 h k) :=
    (continuous_hughesYoungMollifierPairTerm T hh hk).comp continuous_fst
  unfold hughesYoungReducedMellinStaticComplex
  dsimp only
  change Continuous (fun z : ℝ × ℝ =>
    hughesYoungMollifierPairTerm T z.1 h k * (1 / (Real.pi : ℂ)) *
      Complex.exp ((afeCriticalPoint z.1 + (c + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
      Complex.exp ((afeCriticalPoint (-z.1) + (c + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ)))
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hline : Continuous (fun z : ℝ × ℝ =>
      (c : ℂ) + (z.2 : ℂ) * I) := by fun_prop
  have hcrit : Continuous (fun z : ℝ × ℝ => afeCriticalPoint z.1) :=
    hcritical.comp continuous_fst
  have hcritNeg : Continuous (fun z : ℝ × ℝ => afeCriticalPoint (-z.1)) :=
    hcritical.comp (continuous_neg.comp continuous_fst)
  exact (((hmoll.mul continuous_const).mul
    (Complex.continuous_exp.comp ((hcrit.add hline).mul continuous_const))).mul
      (Complex.continuous_exp.comp ((hcritNeg.add hline).mul continuous_const)))

theorem continuous_uncurry_hughesYoungEquation84RegularizedBetaKernel_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (CX COne : ℂ) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84RegularizedBetaKernel x.1
        ((c : ℂ) + (x.2 : ℂ) * I) CX COne) := by
  rw [continuous_iff_continuousAt]
  intro x
  let wfun : ℝ × ℝ → ℂ := fun y => (c : ℂ) + (y.2 : ℂ) * I
  let zfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 - wfun y
  let pfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 + wfun y
  let two : ℝ × ℝ → ℂ := fun y => 2 * wfun y
  have hw : Continuous wfun := by dsimp only [wfun]; fun_prop
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hz : Continuous zfun := by
    dsimp only [zfun]
    exact (hcritical.comp continuous_fst).sub hw
  have hp : Continuous pfun := by
    dsimp only [pfun]
    exact (hcritical.comp continuous_fst).add hw
  have htwo : Continuous two := by dsimp only [two]; fun_prop
  have hzOne : 0 < (zfun x + 1).re := by
    simp [zfun, wfun, afeCriticalPoint]
    linarith
  have hpPos : 0 < (pfun x).re := by
    simp [pfun, wfun, afeCriticalPoint]
    linarith
  have htwoPos : 0 < (two x).re := by
    simp [two, wfun]
    linarith
  have hReg : ContinuousAt (fun y =>
      hughesYoungRegularizedGamma (zfun y)) x :=
    (differentiableAt_hughesYoungRegularizedGamma hzOne).continuousAt.comp
      hz.continuousAt
  have hRegPsi : ContinuousAt (fun y =>
      hughesYoungRegularizedGammaDigamma (zfun y)) x :=
    (differentiableAt_hughesYoungRegularizedGammaDigamma hzOne).continuousAt.comp
      hz.continuousAt
  have hGammaTwo : ContinuousAt (fun y => Complex.Gamma (two y)) x :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos htwoPos).continuousAt.comp
      htwo.continuousAt
  have hGammaP : ContinuousAt (fun y => Complex.Gamma (pfun y)) x :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hpPos).continuousAt.comp
      hp.continuousAt
  have hGammaP0 : Complex.Gamma (pfun x) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hpPos
  have hPsiTwo : ContinuousAt (fun y => Complex.digamma (two y)) x :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one htwoPos).continuousAt.comp
      htwo.continuousAt
  have hPsiP : ContinuousAt (fun y => Complex.digamma (pfun y)) x :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hpPos).continuousAt.comp
      hp.continuousAt
  have hPolyTwo : ContinuousAt (fun y =>
      hughesYoungPolygammaSeries 1 (two y)) x :=
    (hasDerivAt_hughesYoungPolygammaSeries 1 (by norm_num) htwoPos).continuousAt.comp
      htwo.continuousAt
  have hU : ContinuousAt (fun y => -Complex.digamma (two y) + CX) x :=
    hPsiTwo.neg.add_const CX
  have hV : ContinuousAt (fun y =>
      Complex.digamma (pfun y) - Complex.digamma (two y) + COne) x :=
    (hPsiP.sub hPsiTwo).add_const COne
  have hInner : ContinuousAt (fun y =>
      hughesYoungRegularizedGammaDigamma (zfun y) *
          (Complex.digamma (pfun y) - Complex.digamma (two y) + COne) +
        hughesYoungRegularizedGamma (zfun y) *
          ((-Complex.digamma (two y) + CX) *
              (Complex.digamma (pfun y) - Complex.digamma (two y) + COne) +
            hughesYoungPolygammaSeries 1 (two y))) x :=
    (hRegPsi.mul hV).add (hReg.mul ((hU.mul hV).add hPolyTwo))
  have hAll := (hGammaTwo.div hGammaP hGammaP0).mul hInner
  unfold hughesYoungEquation84RegularizedBetaKernel
  dsimp only [zfun, pfun, two, wfun] at hAll ⊢
  exact hAll

set_option maxHeartbeats 1000000 in
theorem continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (CX COne : ℂ) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84RegularizedContourKernel x.1
        ((c : ℂ) + (x.2 : ℂ) * I) CX COne) := by
  rw [continuous_iff_continuousAt]
  intro x
  let wfun : ℝ × ℝ → ℂ := fun y => (c : ℂ) + (y.2 : ℂ) * I
  let pfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 + wfun y
  let qfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint (-y.1) + wfun y
  have hw : Continuous wfun := by dsimp only [wfun]; fun_prop
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hp : Continuous pfun := by
    dsimp only [pfun]
    exact (hcritical.comp continuous_fst).add hw
  have hq : Continuous qfun := by
    dsimp only [qfun]
    exact (hcritical.comp (continuous_neg.comp continuous_fst)).add hw
  have hpPos : 0 < (pfun x).re := by
    simp [pfun, wfun, afeCriticalPoint]
    linarith
  have hqPos : 0 < (qfun x).re := by
    simp [qfun, wfun, afeCriticalPoint]
    linarith
  have hGammaP : ContinuousAt (fun y => Complex.Gammaℝ (pfun y)) x :=
    (differentiableAt_GammaR_of_re_pos hpPos).continuousAt.comp hp.continuousAt
  have hGammaQ : ContinuousAt (fun y => Complex.Gammaℝ (qfun y)) x :=
    (differentiableAt_GammaR_of_re_pos hqPos).continuousAt.comp hq.continuousAt
  have hpole : Continuous (fun y : ℝ × ℝ => afePoleNormalization y.1) :=
    continuous_afePoleNormalization.comp continuous_fst
  have hgammaNorm : Continuous (fun y : ℝ × ℝ => afeGammaNormalization y.1) :=
    continuous_afeGammaNormalization.comp continuous_fst
  have hw0 : wfun x ≠ 0 := by
    intro hx
    have hre := congrArg Complex.re hx
    simp [wfun] at hre
    linarith
  have hbeta : ContinuousAt (fun y : ℝ × ℝ =>
      hughesYoungEquation84RegularizedBetaKernel y.1 (wfun y) CX COne) x := by
    simpa only [wfun] using
      (continuous_uncurry_hughesYoungEquation84RegularizedBetaKernel_vertical
        hc hcHalf CX COne).continuousAt
  have haux : ContinuousAt (fun y : ℝ × ℝ =>
      hughesYoungAuxiliaryZero (wfun y)) x :=
    differentiable_hughesYoungAuxiliaryZero.continuous.continuousAt.comp hw.continuousAt
  have hexp : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2)) x :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (hw.continuousAt.pow 2))
  have hpolyP : ContinuousAt (fun y : ℝ × ℝ =>
      (pfun y * (1 - pfun y)) ^ 2) x :=
    (hp.continuousAt.mul (continuousAt_const.sub hp.continuousAt)).pow 2
  have hpolyQ : ContinuousAt (fun y : ℝ × ℝ => qfun y ^ 2) x :=
    hq.continuousAt.pow 2
  have hnum : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) x :=
    ((((hexp.mul hpolyP).mul hpolyQ).mul (hGammaP.pow 2)).mul (hGammaQ.pow 2))
  have hdivPole : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1) x :=
    hnum.div hpole.continuousAt (afePoleNormalization_ne_zero x.1)
  have hdivW : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1 / wfun y) x :=
    hdivPole.div hw.continuousAt hw0
  have harch : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1 / wfun y / afeGammaNormalization y.1) x :=
    hdivW.div hgammaNorm.continuousAt (afeGammaNormalization_ne_zero x.1)
  have hcore : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2 /
        afePoleNormalization y.1 / wfun y / afeGammaNormalization y.1 *
        hughesYoungEquation84RegularizedBetaKernel y.1 (wfun y) CX COne) x := by
    exact harch.mul hbeta
  unfold hughesYoungEquation84RegularizedContourKernel
    hughesYoungEquation84RegularizedContourKernelCore
  dsimp only [pfun, qfun, wfun] at hcore haux ⊢
  exact haux.mul hcore

theorem continuous_uncurry_hughesYoungEquation84Kernel00_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel00 x.1 ((c : ℂ) + (x.2 : ℂ) * I)) := by
  simpa only [hughesYoungEquation84Kernel00] using
    continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 0

theorem continuous_uncurry_hughesYoungEquation84Kernel10_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel10 x.1 ((c : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel10 hughesYoungEquation84Kernel00
  exact
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 1 0).sub
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 0)

theorem continuous_uncurry_hughesYoungEquation84Kernel01_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel01 x.1 ((c : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel01 hughesYoungEquation84Kernel00
  exact
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 1).sub
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 0)

theorem continuous_uncurry_hughesYoungEquation84Kernel11_vertical
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel11 x.1 ((c : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel11 hughesYoungEquation84Kernel10
    hughesYoungEquation84Kernel01 hughesYoungEquation84Kernel00
  exact
    (((continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 1 1).sub
    ((continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 1 0).sub
      (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
        hc hcHalf 0 0))).sub
    ((continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 1).sub
      (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
        hc hcHalf 0 0))).sub
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_vertical
      hc hcHalf 0 0)

theorem continuous_uncurry_hughesYoungCentralShiftPower_vertical
    (r : ℕ) (c : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungCentralShiftPower r ((c : ℂ) + (z.2 : ℂ) * I)) := by
  unfold hughesYoungCentralShiftPower
  fun_prop

theorem continuous_uncurry_hughesYoungEquation84PositiveOuter_vertical
    (T c : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b r : ℕ) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveOuter T z.1 h k a b r
        ((c : ℂ) + (z.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84PositiveOuter
  exact continuous_const.mul
    ((continuous_uncurry_hughesYoungReducedMellinStaticComplex_vertical
        T c hh hk).mul
      (continuous_uncurry_hughesYoungCentralShiftPower_vertical r c))

theorem continuous_uncurry_hughesYoungEquation84NegativeOuter_vertical
    (T c : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b r : ℕ) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84NegativeOuter T z.1 h k a b r
        ((c : ℂ) + (z.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84NegativeOuter
  exact continuous_const.mul
    ((continuous_uncurry_hughesYoungReducedMellinStaticComplex_vertical
        T c hh hk).mul
      (continuous_uncurry_hughesYoungCentralShiftPower_vertical r c))

set_option maxHeartbeats 1000000 in
theorem continuous_uncurry_hughesYoungEquation84PositiveContourSeries_vertical
    (T : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveContourSeries T z.1 h k a b r
        ((c : ℂ) + (z.2 : ℂ) * I)) := by
  have houter :=
    continuous_uncurry_hughesYoungEquation84PositiveOuter_vertical
      T c hh hk a b r
  have h00 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment a b r false false *
        hughesYoungEquation84Kernel00 z.1 ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul
      (continuous_uncurry_hughesYoungEquation84Kernel00_vertical hc hcHalf)
  have h10 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment a b r true false *
        hughesYoungEquation84Kernel10 z.1 ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul
      (continuous_uncurry_hughesYoungEquation84Kernel10_vertical hc hcHalf)
  have h01 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment a b r false true *
        hughesYoungEquation84Kernel01 z.1 ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul
      (continuous_uncurry_hughesYoungEquation84Kernel01_vertical hc hcHalf)
  have h11 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment a b r true true *
        hughesYoungEquation84Kernel11 z.1 ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul
      (continuous_uncurry_hughesYoungEquation84Kernel11_vertical hc hcHalf)
  refine (houter.mul (((h00.add h10).add h01).add h11)).congr ?_
  intro z
  exact (hughesYoungEquation84PositiveContourSeries_eq_fourMoments
    T z.1 h k a b r ha hb hr ((c : ℂ) + (z.2 : ℂ) * I)).symm

set_option maxHeartbeats 1000000 in
theorem continuous_uncurry_hughesYoungEquation84NegativeContourSeries_vertical
    (T : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84NegativeContourSeries T z.1 h k a b r
        ((c : ℂ) + (z.2 : ℂ) * I)) := by
  have houter :=
    continuous_uncurry_hughesYoungEquation84NegativeOuter_vertical
      T c hh hk a b r
  let negPair : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1, z.2)
  have hnegPair : Continuous negPair := by dsimp only [negPair]; fun_prop
  have hk00 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84Kernel00 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) := by
    simpa only [Function.comp_apply, negPair] using
      (continuous_uncurry_hughesYoungEquation84Kernel00_vertical
        hc hcHalf).comp hnegPair
  have hk10 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84Kernel10 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) := by
    simpa only [Function.comp_apply, negPair] using
      (continuous_uncurry_hughesYoungEquation84Kernel10_vertical
        hc hcHalf).comp hnegPair
  have hk01 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84Kernel01 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) := by
    simpa only [Function.comp_apply, negPair] using
      (continuous_uncurry_hughesYoungEquation84Kernel01_vertical
        hc hcHalf).comp hnegPair
  have hk11 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84Kernel11 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) := by
    simpa only [Function.comp_apply, negPair] using
      (continuous_uncurry_hughesYoungEquation84Kernel11_vertical
        hc hcHalf).comp hnegPair
  have h00 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment b a r false false *
        hughesYoungEquation84Kernel00 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul hk00
  have h10 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment b a r true false *
        hughesYoungEquation84Kernel10 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul hk10
  have h01 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment b a r false true *
        hughesYoungEquation84Kernel01 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul hk01
  have h11 : Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveArithmeticMoment b a r true true *
        hughesYoungEquation84Kernel11 (-z.1) ((c : ℂ) + (z.2 : ℂ) * I)) :=
    continuous_const.mul hk11
  refine (houter.mul (((h00.add h10).add h01).add h11)).congr ?_
  intro z
  exact (hughesYoungEquation84NegativeContourSeries_eq_fourMoments
    T z.1 h k a b r ha hb hr ((c : ℂ) + (z.2 : ℂ) * I)).symm

theorem aestronglyMeasurable_uncurry_hughesYoungFinitePureSignedCentralAtHeight
    {μ ν : Measure ℝ} (T : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight
          T p.1 c p.2 h k a b K) (μ.prod ν) := by
  have hw : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ)) (μ.prod ν) :=
    (Complex.continuous_ofReal.comp
      ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_fst)).aestronglyMeasurable
  simp only [hughesYoungFinitePureSignedCentralAtHeight]
  apply AEStronglyMeasurable.mul hw
  let s := hughesYoungShiftInterval a b
    (hughesYoungFullDyadicBound (K + 1)) (hughesYoungFullDyadicBound (K + 1))
  let f : ℤ → ℝ × ℝ → ℂ := fun r p =>
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k)
  have hm : AEStronglyMeasurable (∑ r ∈ s, f r) (μ.prod ν) := by
    apply Finset.aestronglyMeasurable_sum
    intro r hr
    by_cases hr0 : r = 0
    · simp only [f, hr0, if_true]
      exact aestronglyMeasurable_const
    · simp only [f, hr0, if_false]
      cases r with
      | ofNat n =>
          have hn : 0 < n := by
            by_contra hn0
            apply hr0
            simp [Nat.eq_zero_of_not_pos hn0]
          have hcont :=
            continuous_uncurry_hughesYoungEquation84PositiveContourSeries_vertical
              T hc hcHalf hh hk ha hb hn
          refine hcont.aestronglyMeasurable.congr ?_
          filter_upwards [] with p
          have heq :
              dfiSignedCentralSeries a b (n : ℤ)
                  (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k) =
                hughesYoungEquation84PositiveContourSeries T p.1 h k a b n
                  ((c : ℂ) + (p.2 : ℂ) * I) := by
            rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
                T p.1 c p.2 a b hn,
              hughesYoungEquation83PositiveCentral_eq_equation84
                T p.1 p.2 hc hcHalf h k a b n,
              hughesYoungEquation84Positive_eq_contourSeries
                T p.1 p.2 hcHalf h k a b hn]
          exact heq.symm
      | negSucc m =>
          let n : ℕ := m + 1
          have hn : 0 < n := by dsimp only [n]; omega
          have hrCast : Int.negSucc m = -(n : ℤ) := by
            dsimp only [n]
            omega
          have hcont :=
            continuous_uncurry_hughesYoungEquation84NegativeContourSeries_vertical
              T hc hcHalf hh hk ha hb hn
          refine hcont.aestronglyMeasurable.congr ?_
          filter_upwards [] with p
          have heq :
              dfiSignedCentralSeries a b (-(n : ℤ))
                  (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k) =
                hughesYoungEquation84NegativeContourSeries T p.1 h k a b n
                  ((c : ℂ) + (p.2 : ℂ) * I) := by
            rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
                T p.1 c p.2 a b hn,
              hughesYoungEquation83NegativeCentral_eq_equation84
                T p.1 p.2 hc hcHalf h k a b n,
              hughesYoungEquation84Negative_eq_contourSeries
                T p.1 p.2 hcHalf h k a b hn]
          rw [hrCast]
          exact heq.symm
  have heq : (fun p : ℝ × ℝ => ∑ r ∈ s, f r p) = ∑ r ∈ s, f r := by
    funext p
    exact (Finset.sum_apply p s f).symm
  rw [heq]
  exact hm

/-- Joint continuity of the finite pure signed source in the physical
height and Mellin ordinate.  This is the strong form needed to pass the
active-complement identity through both integrals. -/
theorem continuous_uncurry_hughesYoungFinitePureSignedCentralAtHeight
    (T : ℝ) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight
          T p.1 c p.2 h k a b K) := by
  have hw : Continuous (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_fst)
  simp only [hughesYoungFinitePureSignedCentralAtHeight]
  apply Continuous.mul hw
  let s := hughesYoungShiftInterval a b
    (hughesYoungFullDyadicBound (K + 1)) (hughesYoungFullDyadicBound (K + 1))
  let f : ℤ → ℝ × ℝ → ℂ := fun r p =>
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k)
  have hm : Continuous (∑ r ∈ s, f r) := by
    have hm' : Continuous (fun p => ∑ r ∈ s, f r p) := by
      apply continuous_finsetSum s
      intro r hr
      by_cases hr0 : r = 0
      · simp only [f, hr0, if_true]
        exact continuous_const
      · simp only [f, hr0, if_false]
        cases r with
        | ofNat n =>
            have hn : 0 < n := by
              by_contra hn0
              apply hr0
              simp [Nat.eq_zero_of_not_pos hn0]
            have hcont :=
              continuous_uncurry_hughesYoungEquation84PositiveContourSeries_vertical
                T hc hcHalf hh hk ha hb hn
            refine hcont.congr ?_
            intro p
            have heq :
                dfiSignedCentralSeries a b (n : ℤ)
                    (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k) =
                  hughesYoungEquation84PositiveContourSeries T p.1 h k a b n
                    ((c : ℂ) + (p.2 : ℂ) * I) := by
              rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
                  T p.1 c p.2 a b hn,
                hughesYoungEquation83PositiveCentral_eq_equation84
                  T p.1 p.2 hc hcHalf h k a b n,
                hughesYoungEquation84Positive_eq_contourSeries
                  T p.1 p.2 hcHalf h k a b hn]
            exact heq.symm
        | negSucc m =>
            let n : ℕ := m + 1
            have hn : 0 < n := by dsimp only [n]; omega
            have hrCast : Int.negSucc m = -(n : ℤ) := by
              dsimp only [n]
              omega
            have hcont :=
              continuous_uncurry_hughesYoungEquation84NegativeContourSeries_vertical
                T hc hcHalf hh hk ha hb hn
            refine hcont.congr ?_
            intro p
            have heq :
                dfiSignedCentralSeries a b (-(n : ℤ))
                    (hughesYoungPureReducedMellinWeight T p.1 c p.2 h k) =
                  hughesYoungEquation84NegativeContourSeries T p.1 h k a b n
                    ((c : ℂ) + (p.2 : ℂ) * I) := by
              rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
                  T p.1 c p.2 a b hn,
                hughesYoungEquation83NegativeCentral_eq_equation84
                  T p.1 p.2 hc hcHalf h k a b n,
                hughesYoungEquation84Negative_eq_contourSeries
                  T p.1 p.2 hcHalf h k a b hn]
            rw [hrCast]
            exact heq.symm
    rw [show (∑ r ∈ s, f r) = (fun p => ∑ r ∈ s, f r p) by
      funext p
      exact Finset.sum_apply p s f]
    exact hm'
  have heq : (fun p : ℝ × ℝ => ∑ r ∈ s, f r p) = ∑ r ∈ s, f r := by
    funext p
    exact (Finset.sum_apply p s f).symm
  rw [heq]
  exact hm

/-- The pure signed source is jointly integrable on the bounded Mellin
ordinate and the full physical-height line. -/
theorem integrable_uncurry_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {H : ℝ} (hH : 0 ≤ H) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (K : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight
          T p.1 c p.2 h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) K)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungFinitePureSignedCentralAtHeight
        T p.1 c p.2 h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  let C : Set (ℝ × ℝ) :=
    Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc (-H) H
  have hcontinuous : Continuous f := by
    dsimp only [f]
    exact continuous_uncurry_hughesYoungFinitePureSignedCentralAtHeight
      T hc hcHalf hh hk (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) K
  have hsmall : IntegrableOn f C (volume.prod volume) :=
    hcontinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hbig : IntegrableOn f
      (Set.univ ×ˢ Set.uIoc (-H) H) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (MeasurableSet.univ.prod measurableSet_uIoc)
    intro p hp
    have ht : p.1 ∉ Set.Icc (T / 4) (4 * T) := by
      intro hp1
      apply hp.2
      have hp2 : p.2 ∈ Set.Icc (-H) H := by
        have hu := Set.uIoc_subset_uIcc hp.1.2
        simpa only [Set.uIcc_of_le (by linarith : -H ≤ H)] using hu
      exact ⟨hp1, hp2⟩
    have hzero : hughesYoungHeightWeight T p.1 = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    dsimp only [f]
    simp [hzero]
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa [f] using hbig

end RiemannZeta.GuthMaynard
