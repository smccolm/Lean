import Dubon2026.ArithmeticRelativeIdeleBaseChangeClassZero
import Dubon2026.ArithmeticRelativeSinglePrimeInvariantClass
import Dubon2026.ArithmeticRelativeSinglePrimeTotal
import Dubon2026.ArithmeticRelativeClassOrderFromTotal
import Dubon2026.ArithmeticRelativeClassGeneratorFromIdele

/-! # Construct the original target class generator from actual auxiliary fields

Use one constructed source idele class for normalization, full order and
scaled base-change vanishing, then apply the proved actual tower transfer.
This closes DUB-17's generator-transfer step for the supplied field tower;
constructing a tower satisfying its degree conditions remains necessary.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]

include hLM in
/-- The actual target original class H2 has its exact global degree and a constructed generator whenever the indicated auxiliary cyclic stages and degree divisibility hold; the auxiliary class and its required vanishing are derived. -/
theorem rationalArithmeticRelativeStage_exists_class_generator
    (q r s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclicKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      IsCyclic Gal(L/K))
    (hdegreeKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      letI : Module K L := Algebra.toModule
      Module.finrank K L = q ^ (r + 1))
    (hcyclicEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsCyclic Gal(M/E))
    (hdegreeEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ (s + 1))
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ q ^ (r + 1)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨p, hp, σ, x, _, hx, _⟩ :=
    rationalArithmeticRelativeStage_exists_single_prime_invariant_class
      a K L hKL q r hq hcyclicKL hdegreeKL
  have ht := rationalArithmeticRelativeStageIdeleTotalInvariant_of_representative_values
    a K L hKL x (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ)) _ hx
  have ho := rationalArithmeticRelativeStage_class_order_of_normalized_total
    a K L hKL q r hq hq2 hqa hcyclicKL hdegreeKL x ht
  have hz := rationalArithmeticRelativeStageIdeleBaseChange_scaled_class_zero
    a K E L M hKE hKL hEM hLM q s hq hq2 hqa hcyclicEM hdegreeEM x
    (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
    (q ^ (r + 1)) (pow_pos hq.pos (r + 1)) hd hx
  exact rationalArithmeticRelativeStage_class_generator_of_idele
    a K E L M hKE hKL hEM hLM (q ^ (r + 1)) (pow_ne_zero _ hq.ne_zero) hd x ho hz

end
end Dubon2026
