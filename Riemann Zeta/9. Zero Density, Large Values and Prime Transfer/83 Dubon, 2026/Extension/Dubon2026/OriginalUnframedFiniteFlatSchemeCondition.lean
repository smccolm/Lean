import Dubon2026.OriginalUnframedHopfFlatCondition
import Dubon2026.MatrixAdicFiniteFlatSchemeCondition

/-! # The original geometric finite-flat condition on actual deformation classes -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable (R F K : Type u) {ι O A : Type u}
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The actual geometric finite-flat condition on the original unframed class.
It is defined from the original restricted matrices, using their genuine schemes
at every positive maximal-adic level. -/
def originalUnframedFiniteFlatScheme
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) : OriginalUnframedDeformationClass eA H σ → Prop :=
  Quotient.lift (fun ρ : OriginalContinuousFramedFiber eA H σ =>
    MatrixAdicFiniteFlatScheme R F K (ρ.val.toMonoidHom.comp j)) (by
      intro ρ τ h
      obtain ⟨U, _hU, hc⟩ := h
      apply propext
      exact matrixAdicFiniteFlatScheme_conjugacy_iff
        (ρ.val.toMonoidHom.comp j) (τ.val.toMonoidHom.comp j) U (fun g => hc (j g)))

variable {R F K}

/-- The original class-level coordinate condition is equivalent to its actual
geometric definition. Quotient induction keeps the original representative and
uses the genuine scheme/Hopf equivalence at every original reduction level. -/
theorem originalUnframedHopfFlat_iff_finiteFlatScheme
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H) (c : OriginalUnframedDeformationClass eA H σ) :
    originalUnframedHopfFlat R F K eA H σ j c ↔
      originalUnframedFiniteFlatScheme R F K eA H σ j c := by
  induction c using Quotient.inductionOn with
  | h ρ => exact matrixAdicHopfFlat_iff_finiteFlatScheme (ρ.val.toMonoidHom.comp j)

end
end Dubon2026
