import Dubon2026.OpenSubgroupCharacterFiniteness
import Dubon2026.ArithmeticResidualProfinitePresentation

/-! Finite presentations for original residual representations over the
actual open arithmetic subgroups. This removes the finite-generator input
when the polarized coefficient construction is applied over finite base
fields on DUB-17's source CM route. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- An original open arithmetic subgroup with its inherited profinite topology. -/
abbrev arithmeticOpenSubgroupProfinite (a : 𝓞 ℚ)
    (H : OpenSubgroup (rationalArithmeticGaloisGroup a)) : ProfiniteGrp :=
  closedSubgroupProfinite (rationalArithmeticGaloisGroup a) H.toSubgroup H.isClosed

/-- The actual arithmetic character-finiteness theorem constructs finite
generators and the full residual presentation over every original open base subgroup. -/
theorem arithmeticOpenResidual_has_profinite_presentation
    {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (H : OpenSubgroup (rationalArithmeticGaloisGroup a))
    (ρ : arithmeticOpenSubgroupProfinite a H →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) :
    (let hK := ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ)
     ∃ S : Finset (fixedResidualProfiniteQuotient p (arithmeticOpenSubgroupProfinite a H) ρ.ker hK),
       Function.Surjective (profiniteGeneratorPresentation
         (fixedResidualProfiniteQuotient p (arithmeticOpenSubgroupProfinite a H) ρ.ker hK) S)) := by
  letI : Finite (arithmeticOpenSubgroupProfinite a H ⧸ ρ.ker) :=
    continuousMatrixRepresentation_quotient_finite ρ hρ
  letI : Finite (ρ.ker →ₜ* Multiplicative (ZMod p)) :=
    openSubgroup_continuousCharacters_finite (rationalArithmeticGaloisGroup a)
      (rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite a ha p hp hpa)
      H (continuousMatrixRepresentationKernel ρ hρ).toOpenSubgroup
  exact fixedResidualProfiniteQuotient_has_presentation p hp (arithmeticOpenSubgroupProfinite a H)
    ρ.ker (ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ))

end
end Dubon2026
