import Dubon2026.RationalTwoArithmeticPrincipalPrimeSum
import Dubon2026.ArithmeticRealUnitH2Inflation
import Dubon2026.ArithmeticUnitPrimeInvariant

/-! # Actual finite and real invariant sum of the two-primary carry

The native finite-place pairing and proved real inflation comparison
evaluate the same original inflated carry. The principal product gives
finite support and zero for the sum including the real contribution.
This is the carry step in DUB-17's two-primary arithmetic sum-zero chain;
the application to every descended class and coherent support remain separate.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators NumberField

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete
  arithmeticFiniteCarryGlobalAlgebra arithmeticFiniteCarryTopology arithmeticFiniteCarryDiscrete
  originalRealPeriodQuadratic

variable (a : 𝓞 ℚ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  [hcyc : IsCyclic Gal(E/ℚ)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  {d : ℕ} [NeZero d] (χ : Gal(E/ℚ) →* Multiplicative (ZMod d)) (q : ℚˣ)

omit [IsCyclic Gal(E/ℚ)] in
/-- The literal original finite character carry inflated into the same
arithmetic unit cohomology. Naming it keeps the invariant comparison small. -/
def rationalArithmeticFiniteCarryClass :
    GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a) :=
  galoisUnitFiniteStageH2Inflation E
    (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q))

/-- The existing arithmetic prime invariant evaluates the original
inflated carry by the already proved actual finite reciprocity map. -/
theorem rationalArithmeticFiniteCarryPrimeInvariant (p : ℕ) (hp : p.Prime) :
    rationalArithmeticUnitPrimeInvariant a p hp
      (galoisUnitFiniteStageH2Inflation E
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q))) =
      rationalCyclicInvariant d (χ (@rationalArithmeticFiniteLocalReciprocityAut a E hcyc p hp q)).toAdd :=
  @rationalArithmeticFiniteCarryInvariant a E hcyc p hp _ _ _ _ d _ χ q

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

/-- The same original inflated cyclic carry has finite support of its
actual prime invariants, and their sum plus its actual real invariant is zero. -/
theorem rationalTwoArithmeticCarry_exists_support_sum_zero
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n : ℕ) (hn : 1 ≤ n) [hcycl : IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] :
    let x := rationalArithmeticFiniteCarryClass a E χ q
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
        originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
  let x := rationalArithmeticFiniteCarryClass a E χ q
  obtain ⟨T, hout, hsum⟩ :=
    @rationalTwoArithmeticCyclicSubfield_exists_principal_prime_sum a E hcyc q d _ χ F hEF n hn hcycl
  have hfinite (p : Nat.Primes) : rationalArithmeticUnitPrimeInvariant a p.val p.property x =
      rationalCyclicInvariant d
        (χ (@rationalArithmeticFiniteLocalReciprocityAut a E hcyc p.val p.property q)).toAdd :=
    rationalArithmeticFiniteCarryPrimeInvariant a E χ q p.val p.property
  have hreal := rationalArithmeticRealInflatedCarryInvariant a E χ q
  refine ⟨T, fun p hp => (hfinite p).trans (hout p hp), ?_⟩
  have hs : (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
      ∑ p ∈ T, rationalCyclicInvariant d
        (χ (@rationalArithmeticFiniteLocalReciprocityAut a E hcyc p.val p.property q)).toAdd :=
    Finset.sum_congr rfl (fun p _ => hfinite p)
  exact (congrArg₂ (fun u v : AddCircle (1 : ℚ) => u + v) hs hreal).trans hsum

end
end Dubon2026
