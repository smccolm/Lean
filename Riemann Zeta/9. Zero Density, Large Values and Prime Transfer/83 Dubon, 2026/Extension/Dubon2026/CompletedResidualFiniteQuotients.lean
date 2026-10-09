import Dubon2026.CompletedResidualField
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Finite quotients of the actual original residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- Quotients of the original residual local ring use its canonical ideal quotient structure. -/
instance residualRepresentationLocalRingHasQuotient
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    HasQuotient (ResidualRepresentationLocalRing ρ) (Ideal (ResidualRepresentationLocalRing ρ)) := by
  let quotientStructure := Ideal.instHasQuotient (R := ResidualRepresentationLocalRing ρ)
  exact quotientStructure

private def adicEvaluationQuotientEquiv {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    (AdicCompletion I R ⧸ RingHom.ker (AdicCompletion.evalₐ I n).toRingHom) ≃+*
      (R ⧸ I ^ n) :=
  RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalₐ I n).toRingHom)
    (AdicCompletion.surjective_evalₐ I n)

/-- The actual completed maximal-ideal-power quotient is the corresponding original local coordinate quotient. -/
def completedResidualPowerQuotientEquiv
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) ≃+*
    (ResidualRepresentationLocalRing ρ ⧸
      (RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom) ^ n) := by
  let I := RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom
  letI := residualRepresentationLocalRing_isNoetherian ρ
  have hI : I.FG :=
    (isNoetherianRing_iff_ideal_fg (ResidualRepresentationLocalRing ρ)).mp inferInstance I
  have hker : RingHom.ker (R := ResidualRepresentationCompletion ρ)
      (S := ResidualRepresentationLocalRing ρ ⧸ I ^ n)
      (AdicCompletion.evalₐ (R := ResidualRepresentationLocalRing ρ) I n).toRingHom =
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n := by
    rw [adicCompletion_evaluation_kernel (R := ResidualRepresentationLocalRing ρ) I hI n,
      Ideal.map_pow]
    rw [← completedResidualRepresentationEvaluation_kernel_image ρ,
      completedResidualRepresentationEvaluation_ker ρ]
  let quotientChange := Ideal.quotEquivOfEq hker.symm
  let evaluationEquiv := adicEvaluationQuotientEquiv (R := ResidualRepresentationLocalRing ρ) I n
  let quotientEquiv := quotientChange.trans evaluationEquiv
  exact quotientEquiv

/-- Every original local residual power quotient is finite when the actual coefficient residue field is finite. -/
theorem residualRepresentationLocalRing_finite_quotient [Finite (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    Finite (ResidualRepresentationLocalRing ρ ⧸
      (RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom) ^ n) := by
  let I := RingHom.ker (localizedResidualRepresentationEvaluation ρ).toRingHom
  letI := residualRepresentationLocalRing_isNoetherian ρ
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (R₁ := O) (A := ResidualRepresentationLocalRing ρ) (B := IsLocalRing.ResidueField O)
    (f := localizedResidualRepresentationEvaluation ρ)
    (localizedResidualRepresentationEvaluation_surjective ρ)
  let finiteResidue := Finite.of_injective e e.injective
  letI : Finite (ResidualRepresentationLocalRing ρ ⧸ I) := finiteResidue
  have hI : I.FG :=
    (isNoetherianRing_iff_ideal_fg (ResidualRepresentationLocalRing ρ)).mp inferInstance I
  let finitePowerQuotient := Ideal.finite_quotient_pow
    (R := ResidualRepresentationLocalRing ρ) (I := I) hI n
  exact finitePowerQuotient

/-- All actual maximal-ideal-power quotients of the genuine original completion are finite. -/
theorem residualRepresentationCompletion_finite_quotient [Finite (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    Finite (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n) := by
  letI := residualRepresentationLocalRing_finite_quotient ρ n
  exact Finite.of_injective (completedResidualPowerQuotientEquiv ρ n)
    (completedResidualPowerQuotientEquiv ρ n).injective

end
end Dubon2026
