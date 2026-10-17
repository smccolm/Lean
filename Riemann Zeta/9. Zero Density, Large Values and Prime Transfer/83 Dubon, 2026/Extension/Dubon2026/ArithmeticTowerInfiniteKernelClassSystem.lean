import Dubon2026.ArithmeticInfiniteKernelSystemFromIdele
import Dubon2026.OriginalIntermediateFieldPrimePowerTower
import Dubon2026.ArithmeticAllPrimeScaledClassZero
import Dubon2026.ArithmeticSinglePrimeBaseChangeInfinite
import Dubon2026.ArithmeticRelativeSinglePrimeLiftWitness
import Dubon2026.ArithmeticRelativeSinglePrimeTotal
import Dubon2026.ArithmeticRelativeAllPrimeOrderFromTotal
import Dubon2026.ArithmeticRelativeClassGeneratorFromIdele

/-! # Canonical class invariants from the actual auxiliary tower

Construct the single-prime idele, its full-order class and its scaled
base-change vanishing. The genuine tower degree supplies the remaining
principal-reciprocity premise. This discharges every class-witness and
local-total compatibility input for DUB-17's supplied auxiliary fields.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
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
/-- The supplied actual auxiliary fields construct an injective class invariant with exact image, the total formula on the zero-infinite part and the normalized subgroup restriction system. -/
theorem rationalArithmeticRelativeStage_exists_infinite_kernel_class_system
    (q t r s : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t)
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
    OriginalInfiniteKernelClassInvariantSystem K E
      (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨p, hp, σ, x, hw, hx, _, hy⟩ :=
    rationalArithmeticRelativeStage_exists_single_prime_invariant_lift
      a K L hKL q r hq hcyclicKL hdegreeKL
  have ht := rationalArithmeticRelativeStageIdeleTotalInvariant_of_representative_values
    a K L hKL x (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ)) _ hx
  have hInf : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
      ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0 := by
    letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    obtain ⟨y, hxy⟩ := hy
    intro v
    rw [hxy]
    exact originalFullDecompositionIdeleH2Lift_infinite K L _ hw v y
  have ho := rationalArithmeticRelativeStage_class_order_of_normalized_total_infinite_zero
    a K L hKL q r hq hqa hcyclicKL hdegreeKL x ht hInf
  have hz := rationalArithmeticRelativeStageIdeleBaseChange_scaled_class_zero_of_infinite
    a K E L M hKE hKL hEM hLM q s hq hqa hcyclicEM hdegreeEM x
    (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
    (q ^ (r + 1)) (pow_pos hq.pos (r + 1)) hd hx
    (rationalArithmeticRelativeStageIdeleBaseChange_lift_infinite_zero
      a K E L M hKE hKL hEM hLM _ hw x hy)
  have hdegreeKM := originalIntermediateField_primePower_tower_degree
    (rationalUnramifiedExtension a) K E M hKE hEM q t (s + 1) hdegreeKE hdegreeEM
  exact rationalArithmeticRelativeStage_infinite_kernel_system_of_auxiliary_idele
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalKM := hGalKM)
    a K E L M hKE hKL hEM hLM q (t + s) hq hqa (by simpa only [Nat.add_assoc] using hdegreeKM)
    (q ^ (r + 1)) (pow_ne_zero _ hq.ne_zero) hd x ho hz ht hInf

end
end Dubon2026
