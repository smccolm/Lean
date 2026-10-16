import Dubon2026.OriginalGlobalOddPrimaryH2Killing
import Dubon2026.OriginalCyclotomicContinuousH2Descent

/-! # Exact original cyclic descent for odd-primary global classes

The constructed splitting stage and existing inflation-restriction sequence
give a cyclic class with the same prime-power annihilator. The original
finite-to-continuous comparison preserves its literal inflation in the
same unramified union. This is the cyclic descent input for the generalized
rational reciprocity identity needed by DUB-17's class-invariant route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An original odd-primary global class inside the unramified union descends to a constructed cyclic cyclotomic class with the same annihilator and identical original compositum inflation. -/
theorem originalCyclotomic_exists_odd_primary_globalH2_descent_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra F M := iF.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
      M ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q ^ (r + 1) • y = 0 ∧
        groupCohomology.map (AlgEquiv.restrictNormalHom F) (finiteGaloisUnitTowerInclusion ℚ F M) 2 y =
          groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion ℚ L M) 2 x := by
  obtain ⟨k, F, hk, hcyc, hCyclic, hUnion, hkill⟩ :=
    originalCyclotomic_exists_odd_primary_globalH2_killing_stage L a q r hq hq2 hqa x hx
  refine ⟨k, F, hk, hcyc, hCyclic, hUnion, ?_⟩
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra F M := iF.toAlgebra
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
  letI : FiniteDimensional F M := FiniteDimensional.right ℚ F M
  refine ⟨sup_le hL hUnion, ?_⟩
  exact originalFiniteH2_exists_torsion_descent_of_baseChange_zero ℚ F L M (q ^ (r + 1)) x hx hkill


variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ)

attribute [local instance] originalContinuousCyclicUnionGalois

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The constructed cyclic cyclotomic class retains the original torsion and exactly the same continuous inflation in the original unramified union. -/
theorem originalCyclotomic_exists_odd_primary_continuousH2_descent_stage
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q ^ (r + 1) • x = 0) :
    let U := originalUnramifiedGaloisUnion (Ω := Ω) a
    letI : Algebra L U := (IntermediateField.inclusion hL).toAlgebra
    letI : IsScalarTower ℚ L U := IsScalarTower.of_algHom (IntermediateField.inclusion hL)
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ L) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ L) := ⟨rfl⟩
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q ^ (r + 1) • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            continuousGaloisUnitBaseChangeH2 ℚ ℚ L U
              ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ L)
                (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := L))).symm x) := by
  have hdes := originalCyclotomic_exists_odd_primary_globalH2_descent_stage
    (Ω := Ω) L a q r hq hq2 hqa hL x hx
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
