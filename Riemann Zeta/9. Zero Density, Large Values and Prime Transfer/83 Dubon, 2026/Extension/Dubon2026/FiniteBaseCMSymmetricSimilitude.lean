import Dubon2026.FiniteBaseCMSymmetricRepresentation
import Dubon2026.FiniteBaseCMCharacterComparison

/-! Compute the full original similitude of the constructed polarized
symmetric power. The determinant multiplier on the CM subgroup and the
quadratic component correction give the exact odd source character;
there is no separately assumed whole-group similitude in this step. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra when computing the symmetric-power similitude. -/
local instance finiteBaseCMSymmetricSimilitudeUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K]
  {L : Type*} [Field L] [TopologicalSpace L]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)

/-- The original determinant character with the exact quadratic correction for an odd polarized symmetric power. -/
def finiteBaseCMSymmetricSimilitude : finiteBaseArithmeticGaloisGroup a F →* Lˣ :=
  (GeneralLinearGroup.det.comp ρ.toMonoidHom) ^ n *
    (polarizedComponentSign.comp (finiteBaseQuadraticComponent a F K).toMonoidHom) ^ (n + 1)

/-- On the original CM subgroup the corrected character is exactly the symmetric-power determinant multiplier. -/
theorem finiteBaseCMSymmetricSimilitude_kernel (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMSymmetricSimilitude a F K n ρ g.val = (GeneralLinearGroup.det (ρ g.val)) ^ n := by
  change (GeneralLinearGroup.det (ρ g.val)) ^ n *
    (polarizedComponentSign (finiteBaseQuadraticComponent a F K g.val)) ^ (n + 1) = _
  have hg : finiteBaseQuadraticComponent a F K g.val = 1 := g.property
  rw [hg, map_one, one_pow, mul_one]

variable [IsTotallyReal F] [IsTotallyComplex K]

/-- The exact quadratic correction makes the original real-place character odd in every symmetric degree. -/
theorem finiteBaseCMSymmetricSimilitude_odd
    (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1) :
    finiteBaseCMSymmetricSimilitude a F K n ρ (finiteBaseRealConjugation a F) = -1 := by
  have hd : GeneralLinearGroup.det (ρ (finiteBaseRealConjugation a F)) = -1 := Units.ext hodd
  have hs : (polarizedComponentSign (R := L) (Multiplicative.ofAdd (1 : ZMod 2))) = -1 := by
    change (if (1 : ZMod 2) = 0 then 1 else (-1 : Lˣ)) = -1
    norm_num
  have hp : (-1 : Lˣ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  change (GeneralLinearGroup.det (ρ (finiteBaseRealConjugation a F))) ^ n *
    (polarizedComponentSign (finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F))) ^ (n + 1) = -1
  rw [hd, finiteBaseCMComponent_conjugation, hs, pow_succ, ← mul_assoc, hp, one_mul]

variable [DiscreteTopology L] [Finite L] (hn : (n.factorial : L) ≠ 0)
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The constructed actual polarized symmetric power has this computed original similitude everywhere. -/
theorem finiteBaseCMSymmetricPolarizedRepresentation_similitude (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedSimilitude (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd g) =
      finiteBaseCMSymmetricSimilitude a F K n ρ g := by
  have he : polarizedSimilitude.comp
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd).toMonoidHom =
        finiteBaseCMSymmetricSimilitude a F K n ρ := by
    apply finiteBaseCMCharacter_ext a F K
    · intro x
      change polarizedSimilitude (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd x.val) = _
      rw [finiteBaseCMSymmetricPolarizedRepresentation_kernel, polarizedSimilitude_identityComponent,
        finiteBaseCMSymmetricSimilitude_kernel]
    · change polarizedSimilitude (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd
        (finiteBaseRealConjugation a F)) = _
      rw [finiteBaseCMSymmetricPolarizedRepresentation_odd, finiteBaseCMSymmetricSimilitude_odd a F K n ρ hodd]
  exact DFunLike.congr_fun he g

end
end Dubon2026
