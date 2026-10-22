import Dubon2026.SourceConstantFieldCoordinateMap
import Mathlib.RingTheory.Trace.Basic

/-! DUB-17/18 -> original arithmetic Picard injectivity -> principal-divisor
descent -> finite-basis trace reconstruction. Adapted from
S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, coordinate-map and basis sections.
The existing original degree base change supplies independence from spanning;
the external polynomial denominator-clearing independence proof is omitted.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open Polynomial
variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem trace_algebraMap {x : F} {n : ℕ}
    (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F)
    (y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F')
    (hy : ∀ i, y' i = algebraMap F F' (y i)) (f : F) :
    Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F'
        (algebraMap F F' f) =
      iota K K' F' x (Algebra.trace (IntermediateField.adjoin K ({x} : Set F)) F f) := by
  classical
  have hrepr : ∀ g : F, ∀ i, y'.repr (algebraMap F F' g) i = iota K K' F' x (y.repr g i) := by
    intro g i
    have : algebraMap F F' g = ∑ j, iota K K' F' x (y.repr g j) • y' j := by
      conv_lhs => rw [← y.sum_repr g, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [algebraMap_smul (K' := K') (F' := F'), hy]
    rw [this, y'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace y, Algebra.trace_eq_matrix_trace y']
  simp only [Matrix.trace, Matrix.diag, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hy, ← map_mul,
    hrepr]

theorem eq_sum_trace_mul {x : F} {n : ℕ}
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F)
    (y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F')
    (hy : ∀ i, y' i = algebraMap F F' (y i)) (z : F') :
    z = ∑ i, (Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F'
        (z * algebraMap F F'
          ((Algebra.traceForm (IntermediateField.adjoin K ({x} : Set F)) F).dualBasis
            (traceForm_nondegenerate _ F) y i)) : F') * algebraMap F F' (y i) := by
  classical
  let kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  let kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')
  set yd := (Algebra.traceForm kx F).dualBasis (traceForm_nondegenerate kx F) y with hyd
  suffices h : ∀ i, y'.repr z i = Algebra.trace kx' F' (z * algebraMap F F' (yd i)) by
    conv_lhs => rw [← y'.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i, Algebra.smul_def, hy]
    rfl
  intro i
  let L₁ : F' →ₗ[kx'] kx' := y'.coord i
  let L₂ : F' →ₗ[kx'] kx' :=
    (Algebra.trace kx' F') ∘ₗ (LinearMap.mulRight kx' (algebraMap F F' (yd i)))
  have hL : L₁ = L₂ := by
    refine y'.ext fun j => ?_
    simp only [L₁, L₂, Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
      LinearMap.mulRight_apply]
    rw [hy, ← map_mul, mul_comm, trace_algebraMap y y' hy, ← Algebra.traceForm_apply, hyd,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs with h
    · subst h
      simp
    · rw [map_zero, Finsupp.single_apply, if_neg h]
  exact LinearMap.congr_fun hL z

end
end Dubon2026.SourceCurve.ConstantField
