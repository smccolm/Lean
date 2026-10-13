import Dubon2026.OriginalCyclotomicGlobalH2Killing
import Dubon2026.OriginalFiniteH2BaseChangeDescent

/-! # Original odd-primary global H2 descends to the constructed cyclic stage

The actual cyclotomic killing theorem is consumed by the already proved
exact original inflation-restriction sequence. Both original finite fields
and their actual compositum remain inside the original unramified union;
the descended class retains q-torsion and identical inflation. This is the
finite cyclic reduction needed before DUB-17's principal-product and
carry/cup comparison proves the actual arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- An original odd-primary global class inside the unramified union descends to a constructed cyclic cyclotomic class with the same annihilator and identical original compositum inflation. -/
theorem originalCyclotomic_exists_globalH2_descent_stage
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
    (L : FiniteGaloisIntermediateField ℚ Ω)
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hL : L.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2) (hx : q • x = 0) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      let M := L.toIntermediateField ⊔ F.toIntermediateField
      let iL : L →ₐ[ℚ] M := IntermediateField.inclusion (show L.toIntermediateField ≤ M from le_sup_left)
      let iF : F →ₐ[ℚ] M := IntermediateField.inclusion (show F.toIntermediateField ≤ M from le_sup_right)
      letI : Algebra L M := iL.toAlgebra
      letI : Algebra F M := iF.toAlgebra
      letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom iL
      letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom iF
      M ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
        groupCohomology.map (AlgEquiv.restrictNormalHom F) (finiteGaloisUnitTowerInclusion ℚ F M) 2 y =
          groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion ℚ L M) 2 x := by
  obtain ⟨k, F, hk, hcyc, hCyclic, hUnion, hkill⟩ :=
    originalCyclotomic_exists_globalH2_killing_stage L a q hq hq2 hqa x hx
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
  exact originalFiniteH2_exists_torsion_descent_of_baseChange_zero ℚ F L M q x hx hkill

end
end Dubon2026
