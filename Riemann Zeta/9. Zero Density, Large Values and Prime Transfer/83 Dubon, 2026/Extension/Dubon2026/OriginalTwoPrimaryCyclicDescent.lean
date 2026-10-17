import Dubon2026.OriginalTwoPrimaryGlobalKillingStage
import Dubon2026.OriginalFiniteH2BaseChangeDescent

/-! # Original two-primary cyclic descent with the same annihilator

Actual global killing and the existing inflation-restriction sequence
produce a class over the constructed cyclic subfield. Its inflation is
literally the original class's inflation in the same common extension;
injectivity retains the full original two-power annihilator. This is the
finite descent step toward DUB-17's all-primary invariant sum formula.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An original two-primary class descends to an actual cyclic class with
the same annihilator and identical inflation inside the original union. -/
theorem originalUnramifiedUnion_exists_two_primary_cyclic_descent
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω) (a : 𝓞 ℚ) (r : ℕ)
    (h2a : (2 : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ E : IntermediateField ℚ F,
        ∃ hgal : IsGalois ℚ E,
        letI := hgal
        IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
        let M := L.toIntermediateField ⊔ F.toIntermediateField
        let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
        let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
        let iE : E →ₐ[ℚ] M := iF.comp E.val
        letI : Algebra L M := iL.toAlgebra
        letI : Algebra E M := iE.toAlgebra
        letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
        letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
        M ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ E) 2,
          2 ^ (r + 1) • y = 0 ∧
          groupCohomology.map (AlgEquiv.restrictNormalHom E)
            (finiteGaloisUnitTowerInclusion ℚ E M) 2 y =
          groupCohomology.map (AlgEquiv.restrictNormalHom L)
            (finiteGaloisUnitTowerInclusion ℚ L M) 2 x := by
  obtain ⟨k, F, hk, hcyclo, hF, E, hgal, hcyclic, hcomplex, hkill⟩ :=
    originalUnramifiedUnion_exists_two_primary_globalH2_killing L a r h2a x hx
  letI := hgal
  refine ⟨k, F, hk, hcyclo, hF, E, hgal, hcyclic, hcomplex, ?_⟩
  let M := L.toIntermediateField ⊔ F.toIntermediateField
  let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
  let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
  let iE : E →ₐ[ℚ] M := iF.comp E.val
  letI : Algebra L M := iL.toAlgebra
  letI : Algebra E M := iE.toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := iE.toAlgebra.toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
  letI : FiniteDimensional E M := FiniteDimensional.right ℚ E M
  refine ⟨sup_le hL hF, ?_⟩
  exact originalFiniteH2_exists_torsion_descent_of_baseChange_zero ℚ E L M
    (2 ^ (r + 1)) x hx hkill

end
end Dubon2026
