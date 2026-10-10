import Dubon2026.TopologicalGeneratorsFiniteHom
import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.ArithmeticResidualProfinitePresentation

/-! # Finiteness of all original arithmetic framed lifts over finite coefficients -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Finite A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- For the original arithmetic Galois group, all continuous framed lifts of the given residual representation to any actual finite complete local coefficient ring form a finite set. The original arithmetic character finiteness and fixed-quotient generators are derived. -/
theorem arithmeticOriginalFramedFiber_finite
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    Finite (OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ) := by
  letI : T2Space A := completeLocalAdic_t2Space hA
  letI : Finite (rationalArithmeticGaloisGroup a ⧸ σ.ker) :=
    continuousMatrixRepresentation_quotient_finite σ hσ
  letI : Finite (σ.ker →ₜ* Multiplicative (ZMod p)) :=
    rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite a ha p hp hpa
      (continuousMatrixRepresentationKernel σ hσ).toOpenSubgroup
  let hK := originalResidualMatrixKernel_isClosed (rationalArithmeticGaloisGroup a) σ hσ
  let H := fixedResidualProfiniteQuotient p (rationalArithmeticGaloisGroup a) σ.ker hK
  obtain ⟨S, hS⟩ := fixedResidualQuotient_finitely_generated p hp
    (rationalArithmeticGaloisGroup a) σ.ker hK
  letI : Finite (H →ₜ* GeneralLinearGroup ι A) :=
    finite_continuousMonoidHom_of_topological_generators S hS
  let e := originalFramedFiberFixedQuotientEquiv hA eA p hp
    (rationalArithmeticGaloisGroup a) σ hσ
  exact Finite.of_injective e e.injective

end
end Dubon2026
