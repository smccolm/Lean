import Dubon2026.FiniteBaseCMResidualPresentation
import Dubon2026.FiniteBaseCMSymmetricUniversalSpanning
import Dubon2026.OriginalResidualTraceLocalData

/-! Complete local data of the actual universal CM trace algebra, derived from
the original arithmetic presentation and existing GL trace universality.
This discharges the coefficient-ring prerequisites for DUB-17's
polarization descent; the polarization has not yet descended. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceLocalDataUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual universal CM trace algebra is complete local and Noetherian
in its original topology, which is its own maximal-adic topology. The
arithmetic residual presentation and all coefficient properties are derived. -/
theorem finiteBaseCMSymmetricUniversal_traceAlgebra_localData :
    let T := closedMatrixTraceAlgebra (O := O)
      (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal T) T := by
  letI : Fact p.Prime := ⟨hp⟩
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  have hd := finiteBaseCMSymmetricCoefficientRing_localData a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : IsNoetherianRing Q := hd.1
  letI : IsAdicComplete (IsLocalRing.maximalIdeal Q) Q := hd.2.2
  let eR := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let σ : finiteBaseCMProfiniteGroup a F K →* GeneralLinearGroup (Fin (n + 1))
      (IsLocalRing.ResidueField O) :=
    (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom
  have hσ : Continuous σ := continuous_fst.comp (finiteBaseCMSymmetricMatrices a F K n ρ).continuous
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ)) :=
    finiteBaseCMSymmetricMatrices_absoluteIrreducible a F K p n ρ himage hq hsize hchar
  obtain ⟨S, hS⟩ := finiteBaseCMResidual_has_profinite_presentation a F K ha p hp hpa σ hσ
  exact originalResidualTraceAlgebra_localData
    (L := AlgebraicClosure (IsLocalRing.ResidueField O)) hd.2.1 eR p hp
    (finiteBaseCMProfiniteGroup a F K) σ hσ S hS
    (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa)
    (finiteBaseCMSymmetricUniversalMatrices_residue a F K n ρ hn hodd ν hνk hνc ha p hp hpa) 0

end
end Dubon2026

