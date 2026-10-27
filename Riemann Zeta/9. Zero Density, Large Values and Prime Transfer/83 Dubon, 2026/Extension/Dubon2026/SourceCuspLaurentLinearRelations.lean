import Dubon2026.SourceCuspLaurentSpan
import Dubon2026.SourceCuspLaurentPolynomial
import Dubon2026.SourceLaurentScalarIndependence

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> descent of the actual Fricke span. The existing coefficient-map independence
proof already handles scalar extension. Literal cusp-germ representations
transfer finite linear relations to actual functions, avoiding a new Fourier
independence proof or a common pole-clearing construction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped Manifold

theorem coeffMap_sum_smul {K : Type*} [Field K] [Algebra K ℂ] {ι : Type}
    (s : Finset ι) (c : ι → K) (A : ι → LaurentSeries K) :
    coeffMap (algebraMap K ℂ) (∑ i ∈ s, c i • A i) =
      ∑ i ∈ s, algebraMap K ℂ (c i) • coeffMap (algebraMap K ℂ) (A i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext n
  simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]

theorem CuspTaylor.Represents.cusp_smul_sum {h : ℝ} {ι : Type}
    {A : ι → LaurentSeries ℂ} {f : ι → ℍ → ℂ} (s : Finset ι) (c : ι → ℂ)
    (hr : ∀ i ∈ s, CuspTaylor.Represents (A i) (cuspFunction h (f i))) :
    CuspTaylor.Represents (∑ i ∈ s, c i • A i) (cuspFunction h (∑ i ∈ s, c i • f i)) := by
  have hs := CuspTaylor.Represents.cusp_sum s fun i hi => (hr i hi).cusp_smul (c i)
  convert hs using 1
  congr 1
  funext τ
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem cusp_laurent_sum_smul_eq_zero_iff {h : ℝ} (hh : 0 < h) {ι : Type}
    {A : ι → LaurentSeries ℂ} {f : ι → ℍ → ℂ}
    (hhol : ∀ i, MDiff (f i)) (hper : ∀ i, Function.Periodic (f i ∘ ofComplex) h)
    (hr : ∀ i, CuspTaylor.Represents (A i) (cuspFunction h (f i)))
    (s : Finset ι) (c : ι → ℂ) :
    (∑ i ∈ s, c i • A i) = 0 ↔ (∑ i ∈ s, c i • f i) = 0 := by
  have hrep := CuspTaylor.Represents.cusp_smul_sum s c (fun i _ => hr i)
  have hz : CuspTaylor.Represents 0 (cuspFunction h (0 : ℍ → ℂ)) := by
    simpa only [map_zero] using CuspTaylor.represents_cusp_const h 0
  constructor
  · intro heq
    rw [heq] at hrep
    apply hrep.eq_upperHalfPlane hz hh
    · exact MDifferentiable.sum (t := s) (f := fun i : ι => c i • f i) (fun i _ => MDifferentiable.const_smul (c i) (hhol i))
    · exact mdifferentiable_const
    · intro z
      change (∑ i ∈ s, c i • f i) (ofComplex (z + h)) =
        (∑ i ∈ s, c i • f i) (ofComplex z)
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun w : ℂ => c i * w) (hper i z)
    · intro z; rfl
  · intro heq
    rw [heq] at hrep
    exact hrep.eq_series hz

theorem linearIndependent_functions_of_laurent_coefficients
    {K : Type*} [Field K] [Algebra K ℂ] {h : ℝ} (hh : 0 < h) {ι : Type}
    {A : ι → LaurentSeries K} {f : ι → ℍ → ℂ}
    (hhol : ∀ i, MDiff (f i)) (hper : ∀ i, Function.Periodic (f i ∘ ofComplex) h)
    (hr : ∀ i, CuspTaylor.Represents (coeffMap (algebraMap K ℂ) (A i)) (cuspFunction h (f i)))
    (hf : LinearIndependent K f) : LinearIndependent ℂ f := by
  have hA : LinearIndependent K A := by
    rw [linearIndependent_iff'] at hf ⊢
    intro s c hs i hi
    apply hf s c ?_ i hi
    have hm : (∑ j ∈ s, algebraMap K ℂ (c j) • coeffMap (algebraMap K ℂ) (A j)) = 0 := by
      rw [← coeffMap_sum_smul, hs, map_zero]
    have hfun := (cusp_laurent_sum_smul_eq_zero_iff hh hhol hper hr s
      (fun j => algebraMap K ℂ (c j))).mp hm
    convert hfun using 1
    ext τ
    simp only [Finset.sum_apply, Algebra.smul_def]
    rfl
  have hAC := linearIndependent_coeffMap_algebraMap ℂ hA
  rw [linearIndependent_iff'] at hAC ⊢
  intro s c hs i hi
  exact hAC s c ((cusp_laurent_sum_smul_eq_zero_iff hh hhol hper hr s c).mpr hs) i hi

end
end Dubon2026.SourceFunctionField