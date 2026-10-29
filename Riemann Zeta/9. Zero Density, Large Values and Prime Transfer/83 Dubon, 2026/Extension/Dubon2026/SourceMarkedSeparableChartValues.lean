import Dubon2026.SourceMarkedChartFieldDescent
import Mathlib.FieldTheory.Separable

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> natural chart
descent. A normalized embedding of the separable original coordinate field
sends each function to a root of a separable polynomial over the target
field. Native polynomial lifts transfer the minimal polynomial coefficients;
no perfectness of the target or descent certificate is assumed. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open Polynomial IntermediateField

theorem exists_separable_polynomial_for_coordinate_embedding
    {K F Ω B : Type*} [Field K] [Field F] [Field Ω] [Field B]
    [Algebra K F] [Algebra K Ω] [Algebra K B]
    (x : F) [Algebra.IsSeparable (adjoin K ({x} : Set F)) F]
    (θ : F →ₐ[K] B) (ι : Ω →ₐ[K] B) (c : Ω) (hx : θ x = ι c) (f : F) :
    ∃ q : Ω[X], q.Separable ∧ (q.map ι.toRingHom).IsRoot (θ f) := by
  let Kx := adjoin K ({x} : Set F)
  have hsep : (minpoly Kx f).Separable := Algebra.IsSeparable.isSeparable Kx f
  let φ : Kx →+* B := θ.toRingHom.comp (algebraMap Kx F)
  have hroot : ((minpoly Kx f).map φ).IsRoot (θ f) := by
    rw [IsRoot.def, eval_map]
    change eval₂ (θ.toRingHom.comp (algebraMap Kx F)) (θ.toRingHom f) (minpoly Kx f) = 0
    rw [← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hcoef : ∀ z : Kx, φ z ∈ Set.range ι := by
    let T : IntermediateField K F := comap θ ι.fieldRange
    have hle : Kx ≤ T := by
      apply adjoin_le_iff.mpr
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      change θ x ∈ ι.fieldRange
      exact ⟨c, hx.symm⟩
    intro z
    exact AlgHom.mem_fieldRange.mp (hle z.property)
  have hlift : (minpoly Kx f).map φ ∈ lifts ι.toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hcoef _
  obtain ⟨q, hq⟩ := (mem_lifts _).mp hlift
  refine ⟨q, ?_, ?_⟩
  · rw [← Polynomial.separable_map ι.toRingHom, hq]
    exact hsep.map
  · rw [hq]
    exact hroot

end
end Dubon2026.SourceFunctionField.MarkedChart
