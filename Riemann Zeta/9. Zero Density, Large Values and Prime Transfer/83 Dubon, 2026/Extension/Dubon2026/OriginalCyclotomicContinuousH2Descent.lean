import Dubon2026.OriginalCyclotomicGlobalH2Descent
import Dubon2026.OriginalFiniteH2ContinuousDescent

/-! # Actual cyclic descent inside the original continuous arithmetic extension

The constructed cyclic class has the same continuous inflation in the
original unramified union. All field inclusions and scalar towers come
from its proved compositum containment. This advances the exact arithmetic
source entry needed for DUB-17's global invariant sum-zero theorem.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)

/-- Retain the proved Galois structure on the same original unramified union. -/
local instance originalContinuousCyclicUnionGalois :
    IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The constructed cyclic cyclotomic class retains the original torsion and exactly the same continuous inflation in the original unramified union. -/
theorem originalCyclotomic_exists_continuousH2_descent_stage
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
    letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ L) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ L) := ⟨rfl⟩
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            continuousGaloisUnitBaseChangeH2 ℚ ℚ L U
              ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ L)
                (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := L))).symm x) := by
  have hdes := originalCyclotomic_exists_globalH2_descent_stage
    (Ω := Ω) L a q hq hq2 hqa hL x hx
  obtain ⟨k, F, hk, hcyc, hCyclic, hF, hd⟩ := hdes
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra F M := iF.toAlgebra
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
  obtain ⟨hM, y, hy, hxy⟩ := hd
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
  letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ L) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ L) := ⟨rfl⟩
  letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
  letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
  refine ⟨k, F, hk, hcyc, hCyclic, hF, y, hy, ?_⟩
  let iM : M →ₐ[ℚ] U := IntermediateField.inclusion hM
  letI : Algebra M U := iM.toAlgebra
  letI : IsScalarTower ℚ M U := IsScalarTower.of_algHom iM
  letI : IsScalarTower L M U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F M U := IsScalarTower.of_algebraMap_eq' rfl
  exact originalFiniteH2_continuousInflation_eq_of_finite_inflation_eq ℚ F L M U y x hxy

end
end Dubon2026
