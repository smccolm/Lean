import Dubon2026.FiniteBaseCMSymmetricUniversalMatrices
import Dubon2026.FiniteBaseCMSymmetricIrreducible
import Dubon2026.LocalMatrixRepresentationCentralizer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Actual universal CM matrices span the full matrix algebra by the
original residual comparison, native CM absolute irreducibility and
Nakayama. Native centralizer results then supply the scalar stabilizer
input to DUB-17's unframed polarized trace comparison. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricUniversalSpanUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual original universal CM matrices span the entire matrix algebra over their original polarized coefficient quotient. -/
theorem finiteBaseCMSymmetricUniversalMatrices_span :
    Submodule.span (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa)
      (Set.range (fun g => (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g).val)) = ⊤ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eR := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  have hr : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp r =
      (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom :=
    finiteBaseCMSymmetricUniversalMatrices_residue a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O))
        ((GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp r))) := by
    rw [hr]
    exact finiteBaseCMSymmetricMatrices_absoluteIrreducible a F K p n ρ himage hq hsize hchar
  apply localMatrixRepresentation_span_eq_top_of_reduction
    (L := AlgebraicClosure (IsLocalRing.ResidueField O)) (localCoefficientReduction eR).toRingHom
      (localCoefficientReduction_surjective eR) _ r
  intro x
  change eR (IsLocalRing.residue _ x) = 0 ↔ _
  rw [map_eq_zero]
  exact IsLocalRing.residue_eq_zero_iff
    (R := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) x

include hq hsize hchar himage in
/-- Every matrix centralizing the same original universal CM representation is an original coefficient scalar. -/
theorem finiteBaseCMSymmetricUniversalMatrices_centralizer
    (X : Matrix (Fin (n + 1)) (Fin (n + 1))
      (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
    (hX : ∀ g, X * (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g).val =
      (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g).val * X) :
    ∃ d, X = Matrix.scalar (Fin (n + 1)) d :=
  matrixRepresentation_centralizer_scalar_of_span _
    (finiteBaseCMSymmetricUniversalMatrices_span a F K n ρ hn hodd ν hνk hνc ha p hp hpa hq hsize hchar himage) X hX

include hq hsize hchar himage in
/-- Every invertible change of basis stabilizing the actual original universal CM matrices is an original coefficient unit scalar. -/
theorem finiteBaseCMSymmetricUniversalMatrices_stabilizer
    (U : GeneralLinearGroup (Fin (n + 1))
      (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
    (hU : ∀ g, U * finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g =
      finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g * U) :
    ∃ d, U = GeneralLinearGroup.scalar (Fin (n + 1)) d :=
  matrixRepresentation_stabilizer_scalar_unit_of_span _
    (finiteBaseCMSymmetricUniversalMatrices_span a F K n ρ hn hodd ν hνk hνc ha p hp hpa hq hsize hchar himage) U hU

end
end Dubon2026

