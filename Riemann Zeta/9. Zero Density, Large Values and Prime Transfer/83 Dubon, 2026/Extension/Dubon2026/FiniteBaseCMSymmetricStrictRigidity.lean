import Dubon2026.FiniteBaseCMSymmetricUniversalSpanning
import Dubon2026.PolarizedScalarStabilizer

/-! The actual universal CM polarized deformation has no nonidentity
strict matrix automorphism. Native residual spanning makes a stabilizer
scalar; the original disconnected real element and odd residue
characteristic force that residue-one scalar to equal one. This removes
the strict-automorphism obstruction in DUB-17's unframed comparison. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricStrictRigidityUnionAlgebra (a : 𝓞 ℚ) :
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

variable [CharP (IsLocalRing.ResidueField O) p]
  (hq : 3 < p) (hsize : 2 * n < Nat.card (IsLocalRing.ResidueField O) - 1) (hchar : n < p)
  (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := IsLocalRing.ResidueField O)).range ≤ ρ.toMonoidHom.range)

include hq hsize hchar himage in
/-- The actual universal original polarized CM representation has only the identity strict matrix stabilizer under the original residual image and size conditions. -/
theorem finiteBaseCMSymmetricUniversal_strictStabilizer_eq_one
    (U : GeneralLinearGroup (Fin (n + 1))
      (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
    (hred : letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
      GeneralLinearGroup.map (localCoefficientReduction
        (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
          (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
          (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc))).toRingHom U = 1)
    (hU : ∀ g, polarizedLinearInclusion U *
        finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g =
      finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g *
        polarizedLinearInclusion U) : U = 1 := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eR := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  have hker : ∀ g, U * finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g =
      finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g * U := by
    intro g
    exact polarizedLinear_commute_identity U _
      ((finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc ha p hp hpa g.val).1.trans g.property)
      (hU g.val)
  obtain ⟨u, rfl⟩ := finiteBaseCMSymmetricUniversalMatrices_stabilizer a F K n ρ hn hodd ν hνk hνc ha p hp hpa
    hq hsize hchar himage U hker
  have hr := polarizedScalar_reduction_eq_one (localCoefficientReduction eR).toRingHom u hred
  have hc := (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc ha p hp hpa
    (finiteBaseRealConjugation a F)).1
  rw [finiteBaseCMComponent_conjugation] at hc
  have hi := polarizedScalar_eq_inv_of_commute u _ hc (hU (finiteBaseRealConjugation a F))
  have h2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField O) p 2).mp h)
    omega
  letI : IsLocalHom (localCoefficientReduction eR).toRingHom :=
    inferInstanceAs (IsLocalHom (eR.toRingHom.comp
      (IsLocalRing.residue (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))))
  have hu := localUnit_eq_one_of_eq_inv (localCoefficientReduction eR).toRingHom h2 u hr hi
  rw [hu, map_one]

end
end Dubon2026

