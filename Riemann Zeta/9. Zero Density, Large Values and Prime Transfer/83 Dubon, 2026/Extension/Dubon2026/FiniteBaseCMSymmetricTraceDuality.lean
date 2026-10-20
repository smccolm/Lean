import Dubon2026.FiniteBaseCMSymmetricUniversalPolarization
import Dubon2026.PolarizedTraceDuality
import Dubon2026.PolarizedTraceMultiplier

/-! The actual descended CM matrices have continuous source multiplier
and the conjugate-dual trace identity. Both are derived from the actual
universal polarized representation for DUB-17 polarization descent. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceDualityUnionAlgebra (a : 𝓞 ℚ) :
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

/-- The actual CM trace descent inherits continuity of the prescribed
multiplier and the whole conjugate-dual trace identity. Neither condition
is assumed independently of the original polarized representation. -/
theorem finiteBaseCMSymmetricUniversal_traceDuality
    (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1))
      (closedMatrixTraceAlgebra (O := O)
        (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom))
    (hτ : letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
      MatrixStrictlyConjugate
        (IsLocalRing.residue (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa))
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O)
          (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom)
        (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom) :
    let T := closedMatrixTraceAlgebra (O := O)
      (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
    let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
      (FiniteBaseCMKernel a F K).subtype
    Continuous μ ∧ ∀ g, Matrix.trace (τ (finiteBaseCMConjugation a F K g)).val =
      Matrix.trace (polarizedTwistedDual τ.toMonoidHom μ g).val := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
  let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
    (FiniteBaseCMKernel a F K).subtype
  have hc := polarizedBaseCharacter_subalgebra_continuous
    (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa) ν
    (fun g => (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa g).2) T
  refine ⟨hc.comp continuous_subtype_val, ?_⟩
  apply coefficientPolarization_traceDescent T (IsLocalRing.residue Q) r.toMonoidHom
    τ.toMonoidHom μ (finiteBaseCMConjugation a F K).toMonoidHom
    (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
      (finiteBaseRealConjugation a F)).left.1 hτ
  intro g
  exact finiteBaseCMSymmetricUniversal_CM_duality a F K n ρ hn hodd ν hνk hνc ha p hp hpa g

end
end Dubon2026

