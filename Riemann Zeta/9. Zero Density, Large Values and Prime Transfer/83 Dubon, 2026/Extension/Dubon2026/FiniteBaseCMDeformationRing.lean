import Dubon2026.FiniteBaseCMCharacterComparison
import Dubon2026.FiniteBasePolarizedRepresentation

/-! The actual arithmetic polarized deformation ring consumes the
constructed CM residual extension. Finite generators, the whole-group
residual comparison, continuity and source component are all derived.
The original CM residual matrices and their conjugate-duality identity
remain explicit inputs pending the genuine modular realization in DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the CM deformation-ring consumer. -/
local instance finiteBaseCMDeformationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  (r : FiniteBaseCMKernel a F K →ₜ*
    (GeneralLinearGroup ι (IsLocalRing.ResidueField O) × (IsLocalRing.ResidueField O)ˣ))
  (B : GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hB : B.val.transpose = B.val)
  (hpol : ∀ g, r ((finiteBaseCMGroupSplitting a F K).conjAct
      (Multiplicative.ofAdd (1 : ZMod 2)) g) = (B, 1) * polarizedSwitch (r g) * (B, 1)⁻¹)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K,
    (r g).2 = Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g.val))
  (hνc : ν (finiteBaseRealConjugation a F) = -1)

include hνk hνc in
/-- The original odd base character agrees with the entire constructed residual similitude. -/
theorem finiteBaseCMResidualSimilitude (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedSimilitude (finiteBaseCMPolarizedExtension a F K r B hB hpol g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g) := by
  apply finiteBaseCMPolarizedExtension_similitude a F K r B hB hpol
    ((Units.map ((algebraMap O (IsLocalRing.ResidueField O)).toMonoidHom)).comp ν) hνk
  change Units.map ((algebraMap O (IsLocalRing.ResidueField O)).toMonoidHom)
    (ν (finiteBaseRealConjugation a F)) = (-1 : (IsLocalRing.ResidueField O)ˣ)
  rw [hνc]
  apply Units.ext
  simp

variable [IsNoetherianRing O] (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)

/-- The original arithmetic polarized ring formed from the constructed CM residual representation. -/
abbrev FiniteBaseCMPolarizedCoefficientRing :=
  FiniteBasePolarizedCoefficientRing a F ha p hp hpa (finiteBaseCMPolarizedExtension a F K r B hB hpol) ν

include hνk hνc in
/-- The same original CM residual input makes the actual polarized coefficient ring local. -/
theorem finiteBaseCMPolarizedCoefficientRing_isLocal :
    IsLocalRing (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa) :=
  finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa
    (finiteBaseCMPolarizedExtension a F K r B hB hpol) ν
    (finiteBaseCMResidualSimilitude a F K r B hB hpol ν hνk hνc)

/-- The original CM residual input gives the actual complete local Noetherian polarized coefficient ring. -/
theorem finiteBaseCMPolarizedCoefficientRing_localData :
    (letI := finiteBaseCMPolarizedCoefficientRing_isLocal a F K r B hB hpol ν hνk hνc ha p hp hpa
     IsNoetherianRing (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa) ∧
       IsAdic (IsLocalRing.maximalIdeal (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa)) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa))
         (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa)) :=
  finiteBasePolarizedCoefficientRing_localData a F ha p hp hpa
    (finiteBaseCMPolarizedExtension a F K r B hB hpol) ν
    (finiteBaseCMResidualSimilitude a F K r B hB hpol ν hνk hνc)

/-- The continuous universal representation over the same original CM polarized quotient. -/
@[irreducible] def finiteBaseCMPolarizedUniversalRepresentation :
    finiteBaseArithmeticGaloisGroup a F →ₜ*
      PolarizedGaloisGroup ι (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa) :=
  finiteBasePolarizedUniversalRepresentation a F ha p hp hpa
    (finiteBaseCMPolarizedExtension a F K r B hB hpol) ν
    (finiteBaseCMResidualSimilitude a F K r B hB hpol ν hνk hνc)

/-- The universal representation has the actual CM component and original base similitude. -/
theorem finiteBaseCMPolarizedUniversalRepresentation_characters (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedComponent (finiteBaseCMPolarizedUniversalRepresentation a F K r B hB hpol ν hνk hνc ha p hp hpa g) =
        finiteBaseQuadraticComponent a F K g ∧
      polarizedSimilitude (finiteBaseCMPolarizedUniversalRepresentation a F K r B hB hpol ν hνk hνc ha p hp hpa g) =
        Units.map (algebraMap O (FiniteBaseCMPolarizedCoefficientRing a F K r B hB hpol ν ha p hp hpa)).toMonoidHom (ν g) := by
  unfold finiteBaseCMPolarizedUniversalRepresentation
  have h := finiteBasePolarizedUniversalRepresentation_characters a F ha p hp hpa
    (finiteBaseCMPolarizedExtension a F K r B hB hpol) ν
    (finiteBaseCMResidualSimilitude a F K r B hB hpol ν hνk hνc) g
  exact ⟨h.1.trans (finiteBaseCMPolarizedExtension_component a F K r B hB hpol g), h.2⟩

end
end Dubon2026
