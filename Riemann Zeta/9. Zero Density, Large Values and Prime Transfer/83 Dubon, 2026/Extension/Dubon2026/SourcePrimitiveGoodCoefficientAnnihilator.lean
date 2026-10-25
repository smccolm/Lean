import Dubon2026.SourcePrimitiveGoodAnnihilator
import Dubon2026.SourceFiniteOperatorCoefficientAnnihilator
import Dubon2026.SourcePrimitiveFieldHeckeCharacter
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! DUB-17/18 -> primitive determinant -> original Tate component.
The actual finite integral Hecke algebra supplies an annihilating polynomial
over the literal primitive Fourier coefficient field. This is the arithmetic
descent input for the already proved complex primitive projector. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial TensorProduct
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2

theorem primitiveGoodAnnihilator_coefficient_polynomial (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    ∃ P : Polynomial (sourcePrimitiveCoefficientField f), P.Monic ∧
      aeval (primitiveGoodAnnihilator N f s)
        (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ)) = 0 := by
  let F := sourcePrimitiveCoefficientField f
  let T := sourceOriginalIntegralHeckeAlgebra N 2
  letI : Module.Finite ℤ T := sourceOriginalIntegralHeckeAlgebra_finite N 2 (by norm_num)
  let t (q : {q : Nat.Primes // q.val.Coprime N}) : T :=
    ⟨cuspHeckeLinear N 2 q.val.val, Algebra.subset_adjoin ⟨⟨q.val.val, q.val.property.pos⟩, rfl⟩⟩
  exact finite_operator_coefficient_annihilator (algebraMap F ℂ)
    (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom s t
    (fun q => sourcePrimitiveFieldCoefficient f q.val.val)

end
end Dubon2026
