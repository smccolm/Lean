import Dubon2026.ArithmeticFiniteLocalStageMonotone
import Dubon2026.RationalCyclotomicPrincipalStageBridge

/-! # The same cyclotomic containing field at the actual arithmetic completion

The original global embedding generates the actual local stage. Cyclotomic
uniqueness identifies the containing stage with the one used in the local
conductor-two character proof. Monotonicity then derives containment of the
constructed global subfield's actual completion. This discharges the local
containment input in DUB-17's arithmetic principal-product comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra
  rationalPrimeWittPrime rationalPrimeWittOriginalAlgebra
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- The actual closure stage is cyclotomic of the stated two-power order,
transported from the existing original finite stage. -/
theorem rationalTwoOriginalCyclotomicClosureStage_isCyclotomic
    (n c : ℕ) (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ)
    (hv : v.val = c) (hc : ¬2 ∣ c) :
    IsCyclotomicExtension {2 ^ (n + 1)} (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let F₀ := rationalPrimeOriginalCyclotomicStage 2 Nat.prime_two n
  letI : IsCyclotomicExtension {2 ^ (n + 1)} K F₀ :=
    rationalPrimeOriginalCyclotomicStage_isCyclotomic 2 Nat.prime_two n
  exact IsCyclotomicExtension.equiv {2 ^ (n + 1)} K F₀
    (rationalPrimeOriginalCyclotomicClosureEquiv 2 Nat.prime_two n c v hv hc)

/-- The actual arithmetic local stage of the global two-power cyclotomic
containing field is exactly the field used by the local reciprocity proof.
The full global field need not be cyclic. -/
theorem rationalTwoArithmeticFiniteLocalStage_eq_cyclotomicClosure
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n c : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c) :
    rationalArithmeticFiniteLocalStage a F 2 Nat.prime_two =
      rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let M := rationalArithmeticFiniteLocalStage a F 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
  let N := 2 ^ (n + 1)
  letI : NeZero N := ⟨pow_ne_zero _ (by decide)⟩
  letI : IsCyclotomicExtension {N} K M :=
    embeddedFiniteGaloisCompositum_isCyclotomic_of_primitiveRoot
      (rationalArithmeticFiniteLocalEmbedding a F 2 Nat.prime_two) N
      (IsCyclotomicExtension.zeta_spec N ℚ F)
  letI : IsCyclotomicExtension {N} K C :=
    rationalTwoOriginalCyclotomicClosureStage_isCyclotomic n c v hv hc
  apply FiniteGaloisIntermediateField.val_injective
  exact IntermediateField.isCyclotomicExtension_eq {N} K Ω M.toIntermediateField C.toIntermediateField

/-- Global containment supplies the exact local containment needed by the
cyclic-subfield conductor-two principal-character theorem. -/
theorem rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
    (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n c : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c) :
    (rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two).toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField := by
  have heq := rationalTwoArithmeticFiniteLocalStage_eq_cyclotomicClosure a F n c v hv hc
  rw [← heq]
  exact rationalArithmeticFiniteLocalStage_mono a E F hEF 2 Nat.prime_two

end
end Dubon2026
