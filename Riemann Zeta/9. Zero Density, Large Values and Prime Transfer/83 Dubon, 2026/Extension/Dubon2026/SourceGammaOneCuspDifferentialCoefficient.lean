import Dubon2026.SourceGammaOneIntegralCuspRatio
import Dubon2026.SourceGammaOneIntegralCuspLaurentSpan

/-! DUB-17/18 -> actual Gamma1 differential realization. Integral cusp
generators have coefficients in the original integral-ratio field. The
proved coefficient-field span descent extends their exact q-Euler relation
to every actual cusp form whose Fourier series is valued in that field.
No rationality, integral-basis or field-membership premise remains beyond
the original coefficient-field condition on the cusp form. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceDifferential CongruenceSubgroup
open scoped ModularForm MatrixGroups

theorem exists_cusp_differential_coefficient_of_coeffMap
    {K : Type*} [Field K] [CharZero K] (σ : K →+* ℂ) (N : ℕ) [NeZero N]
    (f : CuspForm (Gamma1 N) 2) (y : PowerSeries K)
    (hy : y.map σ = qExpansion 1 f) :
    ∃ a : qExpFunctionFieldC K (Gamma1 N),
      (a : LaurentSeries K) * qEuler K (jqModC K) = (y : LaurentSeries K) := by
  have hs := gammaOne_laurent_mem_span_integral_of_coeffMap σ N f y hy
  clear hy f
  generalize hz : (y : LaurentSeries K) = z at hs ⊢
  clear hz y
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, p, hp, rfl⟩ := hx
    exact exists_integral_cusp_differential_coefficient K N g p hp
  | zero =>
    refine ⟨0, ?_⟩
    exact zero_mul _
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    change ((a : LaurentSeries K) + (b : LaurentSeries K)) * qEuler K (jqModC K) = x + y
    rw [add_mul, ha, hb]
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨algebraMap K (qExpFunctionFieldC K (Gamma1 N)) c * a, ?_⟩
    change (algebraMap K (LaurentSeries K) c * (a : LaurentSeries K)) *
      qEuler K (jqModC K) = c • x
    rw [mul_assoc, ha, algebraMap_laurentSeries_apply_alt, HahnSeries.single_zero_mul_eq_smul]

end
end Dubon2026.SourceFunctionField.GammaOne
