import Dubon2026.OriginalTwoPrimaryCyclicDescent
import Dubon2026.OriginalNestedStageContinuousInflation

/-! # Two-primary descent retains the original continuous inflation

The same original cyclic class and common finite extension enter the
already proved finite-to-continuous comparison. Literal inclusions give
all scalar towers into the unchanged arithmetic union. This supplies the
continuous comparison needed before DUB-17's two-primary invariant sum.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
  AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] originalContinuousCyclicUnionGalois

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual two-primary cyclic descent has exactly the original
continuous inflation in the same arithmetic union. -/
theorem originalUnramifiedUnion_exists_two_primary_continuous_descent
    (L : FiniteGaloisIntermediateField ℚ Ω) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : 2 ^ (r + 1) • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
    letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ L) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ L) := ⟨rfl⟩
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      ∃ hF : F.toIntermediateField ≤ U,
      ∃ E : IntermediateField ℚ F, ∃ hgal : IsGalois ℚ E,
      letI := hgal
      IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      let iE := (IntermediateField.inclusion hF).comp E.val
      letI : Algebra E U := iE.toAlgebra
      letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iE
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2,
        2 ^ (r + 1) • y = 0 ∧
        continuousGaloisUnitBaseChangeH2 ℚ ℚ E U
          ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ E)
            (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := E))).symm y) =
        continuousGaloisUnitBaseChangeH2 ℚ ℚ L U
          ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ L)
            (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := L))).symm x) := by
  have hdes := originalUnramifiedUnion_exists_two_primary_cyclic_descent
    (Ω := Ω) L a r h2a hL x hx
  obtain ⟨k, F, hk, hcyclo, hF, E, hgal, hd⟩ := hdes
  letI := hgal
  obtain ⟨hcyclic, hcomplex, hd⟩ := hd
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  let iE : E →ₐ[ℚ] M := iF.comp E.val
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra E M := iE.toAlgebra
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
  obtain ⟨_, y, hy, hxy⟩ := hd
  refine ⟨k, F, hk, hcyclo, hF, E, hgal, hcyclic, hcomplex, y, hy, ?_⟩
  exact originalNestedStage_finiteInflation_eq_continuousInflation a L F E hL hF x y hxy

end
end Dubon2026
