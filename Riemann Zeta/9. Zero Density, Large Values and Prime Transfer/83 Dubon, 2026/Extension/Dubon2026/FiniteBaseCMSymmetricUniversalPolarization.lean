import Dubon2026.FiniteBaseCMSymmetricUniversalMatrices
import Dubon2026.FiniteBaseCMConjugation
import Dubon2026.PolarizedConjugateDuality

/-! Extract the actual universal real-place polarization and its CM
conjugate-duality equation. Symmetry and oddness follow from the original
group and source character, as required for DUB-17 polarization descent. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricUniversalPolarizationUnionAlgebra (a : 𝓞 ℚ) :
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

/-- The actual universal real-place element has source similitude minus one. -/
theorem finiteBaseCMSymmetricUniversal_real_odd :
    polarizedSimilitude (finiteBaseCMSymmetricUniversalRepresentation
      a F K n ρ hn hodd ν hνk hνc ha p hp hpa (finiteBaseRealConjugation a F)) = -1 := by
  rw [(finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa (finiteBaseRealConjugation a F)).2, hνc]
  apply Units.ext
  change algebraMap O (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa) (-1) = -1
  simp only [map_neg, map_one]

/-- The actual universal real-place matrix is symmetric; symmetry is
derived from the original arithmetic involution and prescribed odd character. -/
theorem finiteBaseCMSymmetricUniversal_real_symmetric :
    (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
      (finiteBaseRealConjugation a F)).left.1.val.transpose =
      (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
        (finiteBaseRealConjugation a F)).left.1.val := by
  apply polarizedOddInvolution_matrix_symmetric
  · exact (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa (finiteBaseRealConjugation a F)).1.trans (finiteBaseCMComponent_conjugation a F K)
  · exact finiteBaseCMSymmetricUniversal_real_odd a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  · rw [← map_pow, pow_two, finiteBaseRealConjugation_mul_self, map_one]

/-- The original universal CM matrices satisfy the actual conjugate-duality
equation with their original real-place polarization and base multiplier. -/
theorem finiteBaseCMSymmetricUniversal_CM_duality (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
        (finiteBaseCMConjugation a F K g) =
      (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
        (finiteBaseRealConjugation a F)).left.1 *
      (GeneralLinearGroup.scalar (Fin (n + 1))
        (Units.map (algebraMap O (FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa)).toMonoidHom (ν g.val)) *
        polarizedContragredient (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa g)) *
      (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
        (finiteBaseRealConjugation a F)).left.1⁻¹ := by
  let r := finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  have hc := (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa (finiteBaseRealConjugation a F)).1.trans (finiteBaseCMComponent_conjugation a F K)
  have hg := (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa g.val).1.trans g.property
  have he := polarizedOdd_conjugate_identity (r (finiteBaseRealConjugation a F)) (r g.val) hc
    (finiteBaseCMSymmetricUniversal_real_odd a F K n ρ hn hodd ν hνk hνc ha p hp hpa) hg
  rw [(finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa g.val).2] at he
  change (r (finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹)).left.1 = _
  rw [map_mul, map_mul, map_inv]
  exact he

end
end Dubon2026

