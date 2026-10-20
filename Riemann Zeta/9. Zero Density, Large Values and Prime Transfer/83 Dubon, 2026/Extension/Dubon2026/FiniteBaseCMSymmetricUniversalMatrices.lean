import Dubon2026.FiniteBaseCMSymmetricDeformationRing
import Dubon2026.PolarizedIdentityRestriction

/-! The actual original universal polarized representation restricts to
genuine CM general linear matrices, with exact reduction to the original
symmetric power. This is the source entry for native trace descent and
scalar-centralizer results in DUB-17's unframed deformation comparison. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricUniversalMatricesUnionAlgebra (a : 𝓞 ℚ) :
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

/-- The actual original universal symmetric-power matrices on the genuine CM subgroup, with their inherited arithmetic and coefficient topologies. -/
def finiteBaseCMSymmetricUniversalMatrices :
    FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1))
      (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) := by
  let τ := finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let r := τ.toMonoidHom.comp (finiteBaseQuadraticComponent a F K).toMonoidHom.ker.subtype
  have hc : ∀ g, polarizedComponent (r g) = 1 := fun g =>
    (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc ha p hp hpa g.val).1.trans g.property
  exact ⟨polarizedIdentityMatrices r hc,
    polarizedIdentityMatrices_continuous r hc (τ.continuous.comp continuous_subtype_val)⟩

/-- The original universal CM matrices retain every matrix coordinate of the same full polarized representation. -/
theorem finiteBaseCMSymmetricUniversalMatrices_apply (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g =
      (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g.val).left.1 := rfl

/-- The same original universal CM representation reduces to the literal homogeneous symmetric-power matrices of the original rank-two input. -/
theorem finiteBaseCMSymmetricUniversalMatrices_residue :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     (GeneralLinearGroup.map (localCoefficientReduction
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
         (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
         (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc))).toRingHom).comp
       (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom =
       (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom) := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  apply MonoidHom.ext
  intro g
  have h := finiteBasePolarizedUniversalRepresentation_residue a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc) g.val
  rw [finiteBaseCMSymmetricPolarizedRepresentation_kernel] at h
  change GeneralLinearGroup.map _
    ((finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g.val).left.1) =
      homogeneousSymmetricGL n (ρ g.val)
  unfold finiteBaseCMSymmetricUniversalRepresentation
  exact congrArg (fun z : PolarizedGaloisGroup (Fin (n + 1)) (IsLocalRing.ResidueField O) => z.left.1) h

end
end Dubon2026

