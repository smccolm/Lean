import Dubon2026.FiniteBaseCMSymmetricUniversalSpanning
import Dubon2026.OriginalAdicTraceRepresentationDescent

/-! Native continuous trace descent applies to the actual universal CM
matrices over the original polarized coefficient quotient. This is the
CM matrix part of DUB-17's unframed polarized comparison; descent of the
original polarization and the full unframed classification remain open. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceDescentUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual original universal CM matrices descend continuously to their own closed trace algebra by a change of basis reducing to the original identity. -/
theorem finiteBaseCMSymmetricUniversal_traceDescent :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     ∃ τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1))
       (closedMatrixTraceAlgebra (O := O)
         (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom),
       MatrixStrictlyConjugate
         (IsLocalRing.residue (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
         ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O)
           (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom).val.toRingHom).comp
           τ.toMonoidHom)
         (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom) := by
  letI : Fact p.Prime := ⟨hp⟩
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let k := IsLocalRing.ResidueField O
  let C := AlgebraicClosure k
  let eR := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : Algebra (IsLocalRing.ResidueField Q) C :=
    ((algebraMap k C).comp eR.toRingHom).toAlgebra
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := C)
        ((GeneralLinearGroup.map (IsLocalRing.residue Q)).comp r.toMonoidHom))) := by
    change Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := C)
        ((GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp r.toMonoidHom)))
    rw [finiteBaseCMSymmetricUniversalMatrices_residue]
    exact finiteBaseCMSymmetricMatrices_absoluteIrreducible a F K p n ρ himage hq hsize hchar
  have hd := finiteBaseCMSymmetricCoefficientRing_localData a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : IsAdicComplete (IsLocalRing.maximalIdeal Q) Q := hd.2.2
  exact originalAdicContinuousTraceRepresentationDescent_exists (L := C) hd.2.1 eR r 0

end
end Dubon2026

