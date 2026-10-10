import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.ContinuousRepresentationFiniteQuotient
import Dubon2026.FixedResidualProfinitePresentation

/-! # Actual finite-generator residual presentations for the rational arithmetic Galois group -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]

/-- The original continuous arithmetic matrix representation gives an actual presentation on finitely many generators of its whole fixed residual quotient. Original kernel character finiteness and finite residual quotient are both derived; all original relations remain in the actual presentation kernel. -/
theorem rationalArithmeticResidual_has_profinite_presentation
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) :
    (let hK := ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ)
     ∃ S : Finset (fixedResidualProfiniteQuotient p (rationalArithmeticGaloisGroup a) ρ.ker hK),
       Function.Surjective (profiniteGeneratorPresentation
         (fixedResidualProfiniteQuotient p (rationalArithmeticGaloisGroup a) ρ.ker hK) S)) := by
  letI : Finite (rationalArithmeticGaloisGroup a ⧸ ρ.ker) :=
    continuousMatrixRepresentation_quotient_finite ρ hρ
  letI : Finite (ρ.ker →ₜ* Multiplicative (ZMod p)) :=
    rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite a ha p hp hpa
      (continuousMatrixRepresentationKernel ρ hρ).toOpenSubgroup
  exact fixedResidualProfiniteQuotient_has_presentation p hp (rationalArithmeticGaloisGroup a)
    ρ.ker (ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ))

end
end Dubon2026
