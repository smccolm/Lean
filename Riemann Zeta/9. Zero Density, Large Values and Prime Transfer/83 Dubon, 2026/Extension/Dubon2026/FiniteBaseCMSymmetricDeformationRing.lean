import Dubon2026.FiniteBaseCMSymmetricSimilitude
import Dubon2026.FiniteBaseCMDeformationRing

/-! The actual polarized deformation ring consumes the original odd
rank-two representation through its constructed symmetric power. The CM
matrices, polarization and whole-group residual similitude are derived.
The remaining modular realization and local automorphy conditions stay
explicitly outside this DUB-17 arithmetic construction. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricDeformationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
  (hn : (n.factorial : IsLocalRing.ResidueField O) ≠ 0)
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K,
    (GeneralLinearGroup.det (ρ g.val)) ^ n =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g.val))
  (hνc : ν (finiteBaseRealConjugation a F) = -1)

include hνk hνc in
/-- The original base character matches the whole constructed symmetric-power residual similitude. -/
theorem finiteBaseCMSymmetricResidualSimilitude (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedSimilitude (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g) := by
  unfold finiteBaseCMSymmetricPolarizedRepresentation
  exact finiteBaseCMResidualSimilitude a F K _ _ _ _ ν hνk hνc g

variable [IsNoetherianRing O] (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)

/-- The actual arithmetic polarized quotient attached to the original odd rank-two representation and its symmetric power. -/
abbrev FiniteBaseCMSymmetricCoefficientRing :=
  FiniteBasePolarizedCoefficientRing a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν

include hνk hνc in
/-- The constructed original symmetric-power residual input gives a local arithmetic polarized ring. -/
theorem finiteBaseCMSymmetricCoefficientRing_isLocal :
    IsLocalRing (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) :=
  finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)

/-- The original odd rank-two input gives the actual complete local Noetherian polarized symmetric-power coefficient ring. -/
theorem finiteBaseCMSymmetricCoefficientRing_localData :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     IsNoetherianRing (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) ∧
       IsAdic (IsLocalRing.maximalIdeal (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa)) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
         (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa)) :=
  finiteBasePolarizedCoefficientRing_localData a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)

/-- The actual continuous universal polarized representation for the original symmetric-power residual input. -/
@[irreducible] def finiteBaseCMSymmetricUniversalRepresentation :
    finiteBaseArithmeticGaloisGroup a F →ₜ*
      PolarizedGaloisGroup (Fin (n + 1)) (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) :=
  finiteBasePolarizedUniversalRepresentation a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)

/-- The same universal symmetric-power representation retains the actual CM component and original prescribed similitude. -/
theorem finiteBaseCMSymmetricUniversalRepresentation_characters (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedComponent (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g) =
        finiteBaseQuadraticComponent a F K g ∧
      polarizedSimilitude (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g) =
        Units.map (algebraMap O (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa)).toMonoidHom (ν g) := by
  unfold finiteBaseCMSymmetricUniversalRepresentation
  have h := finiteBasePolarizedUniversalRepresentation_characters a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc) g
  exact ⟨h.1.trans (finiteBaseCMSymmetricPolarizedRepresentation_component a F K n ρ hn hodd g), h.2⟩

end
end Dubon2026
