import Dubon2026.FiniteBaseCMSymmetricUniversalPolarization
import Dubon2026.FiniteBaseCMSymmetricRealInvariants
import Dubon2026.FiniteBaseCMSymmetricTraceDescentData
import Dubon2026.LocalCoefficientResidueUniqueness

/-! Original residue compatibility of the real-place and trace-ring
polarizations, needed for strict polarized descent in DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricPolarizationResidueUnionAlgebra (a : 𝓞 ℚ) :
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

variable [IsNoetherianRing O] (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)

/-- The actual universal real-place matrix reduces to the original
symmetric-power residual polarization. -/
theorem finiteBaseCMSymmetricUniversal_real_residue :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
       (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
       (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
     GeneralLinearGroup.map (localCoefficientReduction eQ).toRingHom
       (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
         (finiteBaseRealConjugation a F)).left.1 =
       symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  have h := finiteBasePolarizedUniversalRepresentation_residue a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
    (finiteBaseRealConjugation a F)
  rw [finiteBaseCMSymmetricPolarizedRepresentation_real_place] at h
  unfold finiteBaseCMSymmetricUniversalRepresentation
  exact congrArg (fun z : PolarizedGaloisGroup (Fin (n + 1)) (IsLocalRing.ResidueField O) => z.left.1) h

/-- Every original-base residue identification on the actual closed CM
trace algebra agrees with the original universal coefficient reduction. -/
theorem finiteBaseCMSymmetricTrace_reduction_compatibility :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
       (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
       (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
     let T := closedMatrixTraceAlgebra (O := O)
       (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
     ∀ (hlocal : IsLocalRing T), letI := hlocal
       ∀ eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O,
         localCoefficientReduction eT = (localCoefficientReduction eQ).comp T.val) := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let T := closedMatrixTraceAlgebra (O := O) r
  dsimp only
  intro hlocal eT
  letI : IsLocalRing T := hlocal
  have hd := finiteBaseCMSymmetricCoefficientRing_localData a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : IsLocalHom T.val.toRingHom := originalAdicCoefficientSubalgebra_isLocalHom
    hd.2.1 eQ T (isClosed_closedMatrixTraceAlgebra r)
  exact localCoefficientReduction_subalgebra_eq eQ T eT

end
end Dubon2026

