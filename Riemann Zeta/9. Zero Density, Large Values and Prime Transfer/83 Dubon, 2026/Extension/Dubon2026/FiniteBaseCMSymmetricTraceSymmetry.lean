import Dubon2026.FiniteBaseCMSymmetricTraceIntertwiner
import Dubon2026.PolarizationCongruence
import Dubon2026.PolarizationIntertwinerSymmetry

/-! The actual trace-ring intertwiner is symmetric. Transport it through
the genuine strict matrix descent and compare with the original universal
real-place matrix using the already proved scalar centralizer. This
discharges symmetry in DUB-17 polarization descent. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceSymmetryUnionAlgebra (a : 𝓞 ℚ) :
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
/-- Every actual trace-ring intertwiner of the descended universal CM
matrices is symmetric, by the original universal scalar centralizer and
the original odd real-place matrix; symmetry is not assumed. -/
theorem finiteBaseCMSymmetricTrace_intertwiner_symmetric
    (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1))
      (closedMatrixTraceAlgebra (O := O)
        (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom))
    (B : GeneralLinearGroup (Fin (n + 1)) (closedMatrixTraceAlgebra (O := O)
      (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom))
    (hτ : letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
      MatrixStrictlyConjugate
        (IsLocalRing.residue (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O)
          (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom)
        (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom)
    (hB :
      let T := closedMatrixTraceAlgebra (O := O)
        (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
      let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
        (FiniteBaseCMKernel a F K).subtype
      ∀ g, τ (finiteBaseCMConjugation a F K g) =
        B * polarizedTwistedDual τ.toMonoidHom μ g * B⁻¹) : B.val.transpose = B.val := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let T := closedMatrixTraceAlgebra (O := O) r
  let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
    (FiniteBaseCMKernel a F K).subtype
  let μQ := (Units.map T.val.toMonoidHom).comp μ
  let s := (GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom
  let β := GeneralLinearGroup.map T.val.toRingHom B
  let BQ := (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
    (finiteBaseRealConjugation a F)).left.1
  have hβ := polarization_duality_map T.val.toRingHom τ.toMonoidHom μ
    (finiteBaseCMConjugation a F K).toMonoidHom B hB
  obtain ⟨U, _hU, he⟩ := hτ
  have hr : matrixRepresentationConjugate s U = r :=
    MonoidHom.ext (fun g => (he g).symm)
  have hnew := polarizationCongruence_duality s μQ
    (finiteBaseCMConjugation a F K).toMonoidHom β U hβ
  rw [hr] at hnew
  have hsym := polarizationIntertwiner_symmetric r (polarizedTwistedDual r μQ)
    (finiteBaseCMConjugation a F K).toMonoidHom (finiteBaseCMConjugation_surjective a F K)
    (fun V hV => finiteBaseCMSymmetricUniversalMatrices_stabilizer a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage V hV)
    BQ (polarizationCongruence β U)
    (fun g => finiteBaseCMSymmetricUniversal_CM_duality a F K n ρ hn hodd ν hνk hνc ha p hp hpa g)
    hnew (finiteBaseCMSymmetricUniversal_real_symmetric a F K n ρ hn hodd ν hνk hνc ha p hp hpa)
  have hβsym := (polarizationCongruence_symmetric_iff β U).mp hsym
  ext i j
  exact congrArg (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) Q => X i j) hβsym

end
end Dubon2026

