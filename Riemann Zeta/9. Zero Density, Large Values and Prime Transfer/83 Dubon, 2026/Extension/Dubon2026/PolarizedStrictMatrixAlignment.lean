import Dubon2026.PolarizationScalarAdjustment
import Dubon2026.PolarizationIntertwinerSymmetry
import Dubon2026.TraceCoefficientStrictConjugacy

/-! Align an actual strict CM matrix descent and its original polarization
simultaneously. This is the precise matrix obligation before the DUB-17
whole arithmetic group comparison. -/

namespace Dubon2026
open Matrix IsLocalRing
noncomputable section

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

/-- Original strict matrix descent can be chosen to align the original
polarization as well, using the scalar centralizer and a residue-one square
root. No whole polarized strict equivalence is assumed. -/
theorem polarized_strict_matrix_alignment (h2 : (2 : ResidueField R) ≠ 0)
    (s r : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ) (c : G →* G)
    (hc : Function.Surjective c)
    (hcent : ∀ U : GeneralLinearGroup ι R, (∀ g, U * r g = r g * U) →
      ∃ u : Rˣ, U = GeneralLinearGroup.scalar ι u)
    (B₀ β : GeneralLinearGroup ι R)
    (h₀ : ∀ g, r (c g) = B₀ * polarizedTwistedDual r μ g * B₀⁻¹)
    (hβ : ∀ g, s (c g) = β * polarizedTwistedDual s μ g * β⁻¹)
    (hred : GeneralLinearGroup.map (residue R) β = GeneralLinearGroup.map (residue R) B₀)
    (hs : MatrixStrictlyConjugate (residue R) s r) :
    ∃ W : GeneralLinearGroup ι R, GeneralLinearGroup.map (residue R) W = 1 ∧
      (∀ g, r g = W * s g * W⁻¹) ∧ polarizationCongruence β W = B₀ := by
  obtain ⟨U, hU, he⟩ := hs
  have hr : matrixRepresentationConjugate s U = r := MonoidHom.ext (fun g => (he g).symm)
  have hnew := polarizationCongruence_duality s μ c β U hβ
  rw [hr] at hnew
  obtain ⟨u, hu⟩ := polarizationIntertwiner_scalar r (polarizedTwistedDual r μ) c hc hcent
    B₀ (polarizationCongruence β U) h₀ hnew
  have hnewred : GeneralLinearGroup.map (residue R) (polarizationCongruence β U) =
      GeneralLinearGroup.map (residue R) B₀ := by
    unfold polarizationCongruence
    rw [map_mul, map_mul, map_inv, polarizedContragredient_map, hU, map_one,
      inv_one, one_mul, mul_one, hred]
  obtain ⟨v, hv, hvB⟩ := polarization_scalar_strict_adjustment h2 B₀
    (polarizationCongruence β U) u hu hnewred
  refine ⟨GeneralLinearGroup.scalar ι v * U, ?_, ?_, ?_⟩
  · rw [map_mul, polarizedScalar_map]
    change GeneralLinearGroup.scalar ι (Units.map (residue R).toMonoidHom v) *
      GeneralLinearGroup.map (residue R) U = 1
    rw [hv, map_one, hU, one_mul]
  · intro g
    rw [he g]
    have hvcomm := (polarizedScalar_commute v (U * s g * U⁻¹)).eq
    calc
      U * s g * U⁻¹ = GeneralLinearGroup.scalar ι v * (U * s g * U⁻¹) *
          (GeneralLinearGroup.scalar ι v)⁻¹ := by rw [hvcomm, mul_inv_cancel_right]
      _ = _ := by group
  · rw [polarizationCongruence_mul]
    exact hvB

end
end Dubon2026
