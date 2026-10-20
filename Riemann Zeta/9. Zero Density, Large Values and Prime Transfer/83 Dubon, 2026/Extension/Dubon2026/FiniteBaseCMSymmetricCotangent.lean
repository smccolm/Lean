import Dubon2026.FiniteBaseCMSymmetricDeformationRing
import Dubon2026.FiniteBaseCMSymmetricAdjointInvariants
import Dubon2026.FiniteBasePolarizedCotangent

/-! The original odd rank-two representation supplies the actual CM
symmetric-power coefficient ring and its full-adjoint tangent dimension.
Native arithmetic finite generation, the proved cotangent comparison and
the derived vanishing of invariants remove separate certificates on this
DUB-17 dependency. Source crystalline conditions remain to be imposed. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the actual CM cotangent consumer. -/
local instance finiteBaseCMSymmetricCotangentUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  (p n : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] (hn : n < p)
  (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K,
    (GeneralLinearGroup.det (ρ g.val)) ^ n =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g.val))
  (hνc : ν (finiteBaseRealConjugation a F) = -1)
  (ha : a ≠ 0) (hpa : (p : 𝓞 ℚ) ∣ a)

/-- The actual CM symmetric-power polarized quotient has its original coefficient residue field. -/
def finiteBaseCMSymmetricCoefficientResidueEquiv :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ
       (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc ha p Fact.out hpa
     IsLocalRing.ResidueField (FiniteBaseCMSymmetricCoefficientRing a F K n ρ
       (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν ha p Fact.out hpa) ≃ₐ[O]
         IsLocalRing.ResidueField O) :=
  finiteBasePolarizedCoefficientResidueEquiv a F ha p Fact.out hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc)

/-- The actual original CM symmetric-power cotangent dual is linearly identified with the continuous full-adjoint cocycles of the same original representation. -/
def finiteBaseCMSymmetricCotangentCocycleLinearEquiv :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ
       (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc ha p Fact.out hpa
     OriginalRelativeMaximalCotangentDual
       (finiteBaseCMSymmetricCoefficientResidueEquiv a F K p n hn ρ hodd ν hνk hνc ha hpa) ≃ₗ[IsLocalRing.ResidueField O]
       continuousRepresentationCocyclesOne (polarizedAdjointRep
         (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
           (factorial_cast_ne_zero_of_lt_char p n hn) hodd).toMonoidHom)) :=
  finiteBasePolarizedCotangentCocycleLinearEquiv a F ha p Fact.out hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc)

/-- The genuine original CM symmetric-power cotangent dimension equals its continuous full-adjoint H1 dimension plus the full matrix dimension; the invariant term is derived to vanish. -/
theorem finiteBaseCMSymmetricCotangent_finrank
    (hp : 3 < p) (hsize : 2 * n < Nat.card (IsLocalRing.ResidueField O) - 1)
    (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := IsLocalRing.ResidueField O)).range ≤ ρ.toMonoidHom.range) :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ
       (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc ha p Fact.out hpa
     letI := originalMaximalCotangentResidueModule
       (finiteBaseCMSymmetricCoefficientResidueEquiv a F K p n hn ρ hodd ν hνk hνc ha hpa)
     Module.finrank (IsLocalRing.ResidueField O)
       (RelativeMaximalCotangent O (FiniteBaseCMSymmetricCoefficientRing a F K n ρ
         (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν ha p Fact.out hpa)) =
       Module.finrank (IsLocalRing.ResidueField O)
         (ContinuousRepresentationH1 (polarizedAdjointRep
           (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
             (factorial_cast_ne_zero_of_lt_char p n hn) hodd).toMonoidHom)
           (polarizedAdjointAction_continuous _
             (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
               (factorial_cast_ne_zero_of_lt_char p n hn) hodd).continuous)) + (n + 1) ^ 2) := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ
    (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc ha p Fact.out hpa
  have h := finiteBasePolarizedCotangent_finrank_add_invariants a F ha p Fact.out hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ
      (factorial_cast_ne_zero_of_lt_char p n hn) hodd ν hνk hνc)
  rw [finiteBaseCMSymmetricAdjoint_invariants_eq_bot a F K p n hn ρ hodd hp hsize himage,
    finrank_bot, add_zero, Fintype.card_fin] at h
  exact h

end
end Dubon2026
