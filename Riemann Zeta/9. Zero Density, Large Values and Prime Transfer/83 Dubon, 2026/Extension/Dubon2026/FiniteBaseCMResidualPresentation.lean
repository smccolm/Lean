import Dubon2026.FiniteBaseCMKernel
import Dubon2026.FixedResidualFramedUniversality

/-! Finite residual presentations on the actual CM subgroup. This supplies
the group hypothesis of existing whole-group trace-ring universality on
DUB-17's polarized deformation route, without assuming finite generators. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Preserve the original rational algebra on the arithmetic extension. -/
local instance finiteBaseCMResidualUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] (K : IntermediateField F (rationalUnramifiedExtension a))
  [Algebra.IsQuadraticExtension F K]

/-- The original CM kernel is open because the quadratic component is discrete. -/
theorem finiteBaseCMKernel_isOpen :
    IsOpen (FiniteBaseCMKernel a F K : Set (finiteBaseArithmeticGaloisGroup a F)) :=
  (isOpen_discrete ({1} : Set (Multiplicative (ZMod 2)))).preimage
    (finiteBaseQuadraticComponent a F K).continuous

/-- The same CM kernel with its inherited original profinite topology. -/
abbrev finiteBaseCMProfiniteGroup : ProfiniteGrp :=
  closedSubgroupProfinite (finiteBaseArithmeticGaloisGroup a F)
    (FiniteBaseCMKernel a F K)
    ((FiniteBaseCMKernel a F K).isClosed_of_isOpen (finiteBaseCMKernel_isOpen a F K))

/-- Actual continuous residual CM matrices have a finite surjective profinite
presentation, by the proved arithmetic character-finiteness theorem. -/
theorem finiteBaseCMResidual_has_profinite_presentation
    {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
    (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ρ : finiteBaseCMProfiniteGroup a F K →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hρ : Continuous ρ) :
    ∃ S : Finset (originalResidualProfiniteGroup p (finiteBaseCMProfiniteGroup a F K) ρ hρ),
      Function.Surjective (profiniteGeneratorPresentation
        (originalResidualProfiniteGroup p (finiteBaseCMProfiniteGroup a F K) ρ hρ) S) := by
  let B : OpenSubgroup (rationalArithmeticGaloisGroup a) :=
    ⟨F.fixingSubgroup, F.fixingSubgroup_isOpen⟩
  let C : OpenSubgroup (finiteBaseArithmeticGaloisGroup a F) :=
    ⟨FiniteBaseCMKernel a F K, finiteBaseCMKernel_isOpen a F K⟩
  letI : Finite (finiteBaseCMProfiniteGroup a F K ⧸ ρ.ker) :=
    continuousMatrixRepresentation_quotient_finite ρ hρ
  have hchars : ∀ L : OpenSubgroup (finiteBaseArithmeticGaloisGroup a F),
      Finite (L →ₜ* Multiplicative (ZMod p)) :=
    openSubgroup_continuousCharacters_finite (rationalArithmeticGaloisGroup a)
      (rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite a ha p hp hpa) B
  letI : Finite (ρ.ker →ₜ* Multiplicative (ZMod p)) :=
    openSubgroup_continuousCharacters_finite (finiteBaseArithmeticGaloisGroup a F)
      hchars C (continuousMatrixRepresentationKernel ρ hρ).toOpenSubgroup
  exact fixedResidualProfiniteQuotient_has_presentation p hp (finiteBaseCMProfiniteGroup a F K)
    ρ.ker (originalResidualMatrixKernel_isClosed _ ρ hρ)

end
end Dubon2026
