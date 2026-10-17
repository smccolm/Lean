import Dubon2026.ArithmeticPrimaryAuxiliaryComposita
import Dubon2026.ArithmeticTowerPrimaryOrderClass

/-! # Actual primary-order classes in every allowed mixed-degree stage

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- The actual original idele-class H2 of every finite Galois stage has a constructed class of each prime-power order dividing the target degree when that prime is allowed in the arithmetic union; no auxiliary fields or class witnesses are assumed. -/
theorem rationalArithmeticRelativeStage_exists_prime_power_order_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      q ^ t ∣ Module.finrank K E) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = q ^ t := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨D, r, s, hGalKL, hcyclicKL, hdegreeKL, hGalEM, hcyclicEM, hdegreeEM, hGalKM, hd⟩ :=
    rationalArithmetic_exists_primary_cyclic_auxiliary_composita a K E hKE hGalKE q t hq hqa
  let L := K ⊔ D.toIntermediateField
  let M := E ⊔ D.toIntermediateField
  have hKL : K ≤ L := le_sup_left
  have hEM : E ≤ M := le_sup_left
  have hLM : L ≤ M := sup_le_sup_right hKE D.toIntermediateField
  exact rationalArithmeticRelativeStage_exists_primary_order_class
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalEM := hGalEM) (hGalKM := hGalKM)
    a K E L M hKE hKL hEM hLM q r s (q ^ t) (pow_ne_zero _ hq.ne_zero) hd hq hqa hcyclicKL hdegreeKL hcyclicEM hdegreeEM hdegreeKE

end
end Dubon2026
