import Dubon2026.SourceCuspLaurentFunctionIdentity

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational Fourier
structure -> actual Fricke fractions. A nonzero holomorphic periodic
denominator has a nonzero Laurent germ. The literal identity F*b=a then
identifies F with the Laurent quotient near the cusp, including removable
zeros of b in the upper half-plane; pointwise division is not assumed. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold

theorem Represents.eventually_ne_zero {A : LaurentSeries ℂ} {f : ℂ → ℂ}
    (hf : Represents A f) (hA : A ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), f q ≠ 0 := by
  obtain ⟨a, b, ha, hb, hb0, he, hf⟩ := hf
  have ha0 : (series a : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    exact hA (by rw [he, hz, zero_div])
  have ha0' : series a ≠ 0 := fun hz => ha0 (by rw [hz, map_zero])
  have hb0' : series b ≠ 0 := fun hz => hb0 (by rw [hz, map_zero])
  filter_upwards [hf, eventually_ne_zero_of_series_ne_zero ha ha0',
    eventually_ne_zero_of_series_ne_zero hb hb0'] with q hq haq hbq
  rw [hq]
  exact div_ne_zero haq hbq

theorem Represents.ne_zero_of_function_ne_zero {h : ℝ} {A : LaurentSeries ℂ}
    {f : ℍ → ℂ} (hfA : Represents A (cuspFunction h f))
    (hh : 0 < h) (hf : MDiff f)
    (hper : Function.Periodic (f ∘ ofComplex) h) (hne : f ≠ 0) : A ≠ 0 := by
  intro he
  have hz : Represents A (cuspFunction h (0 : ℍ → ℂ)) := by
    simpa only [he, map_zero] using represents_cusp_const h 0
  exact hne (hfA.eq_upperHalfPlane hz hh hf mdifferentiable_const hper (by
    intro z
    rfl))

theorem Represents.cusp_of_mul_eq {h : ℝ} {A B : LaurentSeries ℂ} {a b f : ℍ → ℂ}
    (ha : Represents A (cuspFunction h a)) (hb : Represents B (cuspFunction h b))
    (hb0 : B ≠ 0) (hrel : f * b = a) :
    Represents (A / B) (cuspFunction h f) := by
  apply (ha.cusp_div hb).congr
  filter_upwards [self_mem_nhdsWithin, hb.eventually_ne_zero hb0] with q hq hbq
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.div_apply] at hbq ⊢
  exact (eq_div_iff hbq).mpr (congrFun hrel _)

end
end Dubon2026.SourceFunctionField.CuspTaylor