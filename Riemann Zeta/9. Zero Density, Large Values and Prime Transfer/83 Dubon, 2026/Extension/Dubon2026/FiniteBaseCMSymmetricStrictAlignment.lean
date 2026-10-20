import Dubon2026.FiniteBaseCMSymmetricPolarizationResidue
import Dubon2026.PolarizedStrictMatrixAlignment

/-! A single original residue-one basis change aligns both the CM trace
matrices and the original universal polarization, as required for the
full arithmetic polarized comparison on DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricStrictAlignmentUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual trace-ring descent and original residual polarization
have one strict universal basis change aligning both matrix data. -/
theorem finiteBaseCMSymmetricTrace_strict_alignment :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
     let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp (FiniteBaseCMKernel a F K).subtype
     ∀ (hlocal : IsLocalRing T), letI := hlocal
       ∀ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1)) T)
         (B : GeneralLinearGroup (Fin (n + 1)) T),
         GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom B =
           symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)) →
         MatrixStrictlyConjugate (IsLocalRing.residue Q)
           ((GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom) r.toMonoidHom →
         (∀ g, τ (finiteBaseCMConjugation a F K g) = B * polarizedTwistedDual τ.toMonoidHom μ g * B⁻¹) →
         ∃ W : GeneralLinearGroup (Fin (n + 1)) Q,
           GeneralLinearGroup.map (IsLocalRing.residue Q) W = 1 ∧
           (∀ g, r g = W * GeneralLinearGroup.map T.val.toRingHom (τ g) * W⁻¹) ∧
           polarizationCongruence (GeneralLinearGroup.map T.val.toRingHom B) W =
             (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
               (finiteBaseRealConjugation a F)).left.1) := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let T := closedMatrixTraceAlgebra (O := O) r
  let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp (FiniteBaseCMKernel a F K).subtype
  let μQ := (Units.map T.val.toMonoidHom).comp μ
  let BQ := (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
    (finiteBaseRealConjugation a F)).left.1
  dsimp only
  intro hlocal eT τ B hBred hτ hB
  letI : IsLocalRing T := hlocal
  have hd := finiteBaseCMSymmetricCoefficientRing_localData a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  letI : IsAdicComplete (IsLocalRing.maximalIdeal Q) Q := hd.2.2
  have hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField O) p 2).mp h)
    omega
  have h2 : (2 : IsLocalRing.ResidueField Q) ≠ 0 := by
    intro h
    apply hk2
    simpa only [map_ofNat, map_zero] using congrArg eQ h
  let s := (GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom
  let β := GeneralLinearGroup.map T.val.toRingHom B
  have hcompat := finiteBaseCMSymmetricTrace_reduction_compatibility a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa hlocal eT
  have hβred : GeneralLinearGroup.map (localCoefficientReduction eQ).toRingHom β =
      GeneralLinearGroup.map (localCoefficientReduction eQ).toRingHom BQ := by
    rw [finiteBaseCMSymmetricUniversal_real_residue]
    change GeneralLinearGroup.map ((localCoefficientReduction eQ).comp T.val).toRingHom B = _
    rw [← hcompat]
    exact hBred
  have hred : GeneralLinearGroup.map (IsLocalRing.residue Q) β =
      GeneralLinearGroup.map (IsLocalRing.residue Q) BQ := by
    apply Units.ext
    ext i j
    apply eQ.injective
    exact congrArg (fun M : GeneralLinearGroup (Fin (n + 1)) (IsLocalRing.ResidueField O) => M.val i j) hβred
  exact polarized_strict_matrix_alignment h2 s r μQ (finiteBaseCMConjugation a F K).toMonoidHom
    (finiteBaseCMConjugation_surjective a F K)
    (fun U hU => finiteBaseCMSymmetricUniversalMatrices_stabilizer a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage U hU)
    BQ β (fun g => finiteBaseCMSymmetricUniversal_CM_duality a F K n ρ hn hodd ν hνk hνc ha p hp hpa g)
    (polarization_duality_map T.val.toRingHom τ.toMonoidHom μ (finiteBaseCMConjugation a F K).toMonoidHom B hB)
    hred hτ

end
end Dubon2026

