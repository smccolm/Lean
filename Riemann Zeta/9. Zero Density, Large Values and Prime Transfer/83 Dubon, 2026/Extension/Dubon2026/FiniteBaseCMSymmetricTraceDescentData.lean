import Dubon2026.FiniteBaseCMSymmetricTraceLocalData
import Dubon2026.FiniteBaseCMSymmetricTraceDescent
import Dubon2026.CoefficientSubalgebraResidue
import Dubon2026.MatrixStrictConjugacyCoefficientChange

/-! The actual complete local CM trace ring, its genuine residue equivalence
and continuous descended matrices with the original residual representation.
These are the coefficient objects required for DUB-17 polarization descent. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceDescentDataUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual universal CM matrices descend over their own complete local
trace algebra, with its genuine residue field and exact original residual
representation, by a conjugator reducing to the identity. -/
theorem finiteBaseCMSymmetricUniversal_traceDescentData :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
     let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
       (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
       (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
     let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     ∃ hlocal : IsLocalRing T,
       letI := hlocal
       IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
       ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1)) T),
         localCoefficientReduction eT = (localCoefficientReduction eQ).comp T.val ∧
         (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom =
           (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom ∧
         MatrixStrictlyConjugate (IsLocalRing.residue Q)
           ((GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom) r.toMonoidHom) := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  have hd := finiteBaseCMSymmetricCoefficientRing_localData a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
  obtain ⟨hlocal, hnoeth, htop, hcomplete⟩ :=
    finiteBaseCMSymmetricUniversal_traceAlgebra_localData a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage
  letI : IsLocalRing T := hlocal
  letI : IsLocalHom T.val.toRingHom := originalAdicCoefficientSubalgebra_isLocalHom
    hd.2.1 eQ T (isClosed_closedMatrixTraceAlgebra r.toMonoidHom)
  let eT := coefficientSubalgebraResidueEquiv eQ T
  obtain ⟨τ, hτ⟩ := finiteBaseCMSymmetricUniversal_traceDescent a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa hq hsize hchar himage
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, coefficientSubalgebraReduction_eq eQ T, ?_, hτ⟩
  rw [coefficientSubalgebraReduction_eq]
  have hr := matrixStrictlyConjugate_reduction (localCoefficientReduction eQ).toRingHom
    ((GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom) r.toMonoidHom
    (matrixStrictlyConjugate_comp_reduction (IsLocalRing.residue Q) eQ.toRingHom _ _ hτ)
  exact hr.symm.trans
    (finiteBaseCMSymmetricUniversalMatrices_residue a F K n ρ hn hodd ν hνk hνc ha p hp hpa)

end
end Dubon2026

