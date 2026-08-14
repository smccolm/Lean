import RiemannZeta.GuthMaynard.DFIEquation24
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap

#check SchwartzMap.decay
#check SchwartzMap.fourier_coe
#check Real.fourier_eq
#check MeasureTheory.Measure.volume_eq_prod
#check MeasureTheory.integral_integral_swap_of_hasCompactSupport
#check integrable_one_add_norm
#check Complex.norm_exp
#check Prod.norm_def
#check SchwartzMap.integrable
#check SchwartzMap.integrable_pow_mul
#check MeasureTheory.integral_prod
#check MeasureTheory.Integrable.integrableOn
#check MeasureTheory.Integrable.mono'
#check MeasureTheory.Integrable.comp_smul
#check MeasureTheory.Integrable.integral_prod_right
#check MeasureTheory.Integrable.integral_prod_left
#check MeasureTheory.integrable_prod_iff
#check WithLp.prod_inner_apply
#check WithLp.volume_preserving_ofLp
#check WithLp.volume_preserving_toLp
#check MeasurePreserving.integral_comp
#check MeasurePreserving.integrable_comp_emb
#check MeasureTheory.integral_prod_mul
#check HasCompactSupport.mul_left
#check HasCompactSupport.mul_right
#check MeasurableEquiv.toLp
#check MeasureSpace
#check Measure.IsAddHaarMeasure
#check WithLp.norm_fst_le
#check Real.fourierChar
#check RCLike.inner_apply
#check real_inner_comm

example (r s u v : ℝ) :
    𝐞 (-inner ℝ (WithLp.toLp 2 (r, s)) (WithLp.toLp 2 (u, v))) =
      𝐞 (-(r * u + s * v)) := by
  simp only [WithLp.prod_inner_apply]
  congr 1
  simp
  ring

example (r s u v : ℝ) :
    𝐞 (-(r * u + s * v)) = 𝐞 (-(r * u)) * 𝐞 (-(s * v)) := by
  rw [show -(r * u + s * v) = -(r * u) + -(s * v) by ring]
  exact AddChar.map_add_eq_mul Real.fourierChar _ _

#check Summable.mul_prod
#check Summable.prod
#check Summable.prod_factor
#check HasSum.mul
#check Summable.tsum_mul_tsum
