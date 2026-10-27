import Dubon2026.SourceGammaOneRationalBoundedDenominators
import Dubon2026.SourceLaurentSpanDescent
import Dubon2026.SourceHasseCoefficientTransport

/-! DUB-17/18 -> actual Gamma1 differential realization. The proved
integral cusp spanning theorem gives a finite complex scalar expression
for the original cusp form. Coefficientwise Laurent retraction descends
that expression to its actual coefficient field. This avoids selecting a
new rational basis or developing a field-intersection theorem. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceFricke CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_laurent_mem_span_integral_of_coeffMap
    {K : Type*} [Field K] (σ : K →+* ℂ) (N : ℕ) [NeZero N]
    (f : CuspForm (Gamma1 N) 2) (y : PowerSeries K)
    (hy : y.map σ = qExpansion 1 f) :
    (y : LaurentSeries K) ∈ Submodule.span K
      {x : LaurentSeries K | ∃ (g : CuspForm (Gamma1 N) 2) (p : PowerSeries ℤ),
        IsIntegralQExp g p ∧ intSeriesC K p = x} := by
  let T : Set (CuspForm (Gamma1 N) 2) := {g | ∃ p : PowerSeries ℤ, IsIntegralQExp g p}
  let S : Set (LaurentSeries K) := {x | ∃ (g : CuspForm (Gamma1 N) 2) (p : PowerSeries ℤ),
    IsIntegralQExp g p ∧ intSeriesC K p = x}
  let Q : CuspForm (Gamma1 N) 2 →ₗ[ℂ] LaurentSeries ℂ :=
    { toFun g := (qExpansion 1 g : LaurentSeries ℂ)
      map_add' g h := by
        rw [CuspForm.coe_add,
          ModularForm.qExpansion_add zero_lt_one (gammaOne_one_mem_strictPeriods N) g h,
          PowerSeries.coe_add]
      map_smul' c g := by
        rw [CuspForm.IsGLPos.coe_smul,
          ModularForm.qExpansion_smul zero_lt_one (gammaOne_one_mem_strictPeriods N) c g,
          PowerSeries.coe_smul, RingHom.id_apply] }
  have hf : f ∈ Submodule.span ℂ T := by
    rw [show Submodule.span ℂ T = ⊤ from span_gammaOne_weightTwo_integral_cuspForms_eq_top N]
    trivial
  have hQf : Q f ∈ Submodule.span ℂ (Q '' T) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩
  have hspan : Submodule.span ℂ (Q '' T) ≤ Submodule.span ℂ (coeffMap σ '' S) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, ⟨p, hp⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨intSeriesC K p, ⟨g, p, hp, rfl⟩, ?_⟩
    have hmap : coeffMap σ (intSeriesC K p) = intSeriesC ℂ p := by
      rw [intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
      congr 1
      ext n
      simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]
    rw [hmap]
    exact congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hp
  apply mem_span_of_coeffMap_mem_span σ S (y : LaurentSeries K)
  rw [coeffMap_ofPowerSeries, hy]
  exact hspan hQf

end
end Dubon2026.SourceFunctionField.GammaOne
