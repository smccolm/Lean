import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Int

/-! Elementary integer-to-complex coordinate transport used by the
actual Hecke basis. Keeping this algebraic calculation abstract avoids
unfolding the concrete modular-form field during scalar inference.
-/
namespace Dubon2026
noncomputable section

theorem finiteIntegerOperatorAlgebra_free (M : Type*) [AddCommGroup M]
    [Module ℂ M] (T : Subalgebra ℤ (Module.End ℂ M)) [Module.Finite ℤ T] :
    Module.Free ℤ T := by
  letI : Module.IsTorsionFree ℤ (Module.End ℂ M) := Module.IsTorsionFree.trans ℂ
  letI : Module.IsTorsionFree ℤ T :=
    Subtype.val_injective.moduleIsTorsionFree (fun t : T => t.val) (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

variable {B : Type*} [Ring B] [Algebra ℂ B]
variable (T : Subalgebra ℤ B) (A : Subalgebra ℂ B) (h : T ≤ A.restrictScalars ℤ)

/-- Inclusion of an integer algebra into a containing complex algebra. -/
def integralComplexAlgebraInclusion : T →ₐ[ℤ] A := Subalgebra.inclusion h

theorem integralComplexAlgebraInclusion_apply (t : T) :
    (integralComplexAlgebraInclusion T A h t).val = t.val := rfl

theorem integralComplexAlgebraInclusion_basis {ι : Type*}
    (b : Module.Basis ι ℤ T) (c : Module.Basis ι ℂ A)
    (hc : ∀ i, (c i).val = (b i).val) (i : ι) :
    integralComplexAlgebraInclusion T A h (b i) = c i := Subtype.ext (hc i).symm

theorem integralComplexAlgebraInclusion_repr {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ T) (c : Module.Basis ι ℂ A)
    (hc : ∀ i, (c i).val = (b i).val) (t : T) (i : ι) :
    c.repr (integralComplexAlgebraInclusion T A h t) i = (b.repr t i : ℂ) := by
  classical
  conv_lhs => rw [← b.sum_repr t]
  simp only [map_sum, map_zsmul, integralComplexAlgebraInclusion_basis T A h b c hc,
    Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end
end Dubon2026
