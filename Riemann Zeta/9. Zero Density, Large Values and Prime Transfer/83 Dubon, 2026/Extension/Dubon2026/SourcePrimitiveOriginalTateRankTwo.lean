import Dubon2026.SourceOriginalCuspTateRankTwo
import Dubon2026.SourcePrimitiveHeckeAlgebraRankTwo
import Dubon2026.SourcePrimitiveOriginalTateEvaluation

/-! DUB-17/18 -> primitive Frobenius determinant -> the nonzero primitive
Tate component. The actual integral Hecke action, original rank-two Tate
coordinates and prescribed primitive character discharge every algebraic
input to the rank-two image theorem. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
open scoped IsMulCommutative

theorem exists_primitive_originalTate_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : (sourcePrimitiveCoefficientField f)[X]), P.eval 0 = 1 ∧
      IsIdempotentElem (primitiveGoodTensorProjector N f s P) ∧
      Nonempty ((primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorProjector N f s P)).range ≃ₗ[E] (Fin 2 → E)) := by
  let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
  letI : IsMulCommutative T :=
    SourceHeckeMatrixDescent.Tp_commutative (originalLatticeHeckeMatrix N b lb) p
  letI : CommRing T := inferInstance
  exact exists_primitive_heckeAction_rankTwo N f τ
    (originalCuspRationalTateHecke N p b P₀ lb)
    (originalCuspPadicHeckeMap N p b lb)
    (originalPadicHeckeEigencharacter N p b lb f τ)
    (originalCuspPadicHeckeMap_character N p b lb f τ)
    (originalCuspPadicHeckeMap_generates N p b lb)
    (originalCuspTate_rankTwo N p b P₀ lb)

end
end Dubon2026.SourceFunctionField.OriginalChart
