import Dubon2026.FiniteBaseArithmeticResidualPresentation
import Dubon2026.QuadraticGaloisComponent

/-! The actual quadratic component character on the original finite-base
arithmetic Galois group. This identifies the source CM extension's component
kernel without an independently supplied character certificate for DUB-17. -/

namespace Dubon2026
open Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra on the arithmetic Galois extension. -/
local instance finiteBaseQuadraticUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K]

/-- The original quadratic Galois restriction gives the continuous arithmetic component character. -/
def finiteBaseQuadraticComponent :
    finiteBaseArithmeticGaloisGroup a F →ₜ* Multiplicative (ZMod 2) :=
  ⟨(quadraticGaloisComponent K).comp (finiteBaseArithmeticGaloisEquiv a F).toMonoidHom,
    (quadraticGaloisComponent_continuous K).comp (finiteBaseArithmeticGaloisEquiv_continuous a F)⟩

/-- Trivial component means fixing every element of the original quadratic field. -/
theorem finiteBaseQuadraticComponent_eq_one_iff (g : finiteBaseArithmeticGaloisGroup a F) :
    finiteBaseQuadraticComponent a F K g = 1 ↔
      ∀ x : K, finiteBaseArithmeticGaloisEquiv a F g (x : rationalUnramifiedExtension a) = x := by
  change quadraticGaloisComponent K (finiteBaseArithmeticGaloisEquiv a F g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, quadraticGaloisComponent_ker, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩

/-- Both source components occur in the same original arithmetic Galois group. -/
theorem finiteBaseQuadraticComponent_surjective :
    Function.Surjective (finiteBaseQuadraticComponent a F K) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  exact (quadraticGaloisComponent_surjective K).comp (finiteBaseArithmeticGaloisEquiv a F).surjective

end
end Dubon2026
