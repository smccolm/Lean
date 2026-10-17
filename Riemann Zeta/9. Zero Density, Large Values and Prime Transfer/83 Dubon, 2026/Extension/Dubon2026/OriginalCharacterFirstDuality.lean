import Dubon2026.OriginalCharacterHomologyFunctionals

/-! # Original first-cohomology character duality

The actual character-valued first cohomology is linearly equivalent to
the linear functionals on original first homology. This removes the
ordinary degree-one duality assumption in DUB-17's finite class/Ext
route. Comparison with the arithmetic fundamental class and integral
degree-two connecting maps remains a separate obligation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
variable (Q : Type) [AddCommGroup Q] [Module k Q] [Module.Injective k Q]
variable (M : Rep.{0} k G)

private def originalCharacterCohomologyQuotientLift :
    (groupCohomology.cocycles₁ (originalLinearCharacterRep Q M) ⧸
      LinearMap.ker (groupCohomology.H1π (originalLinearCharacterRep Q M)).hom) →ₗ[k]
        (groupHomology M 1 →ₗ[k] Q) :=
  (LinearMap.ker (groupCohomology.H1π (originalLinearCharacterRep Q M)).hom).liftQ
    (originalCharacterHomologyEvaluationLinear Q M)
    (fun c hc => (originalCharacterHomologyEvaluation_eq_zero_iff Q M c).mpr hc)

/-- Evaluation pairing descended to actual first cohomology and actual first homology. -/
def originalCharacterFirstPairing :
    groupCohomology (originalLinearCharacterRep Q M) 1 →ₗ[k]
      (groupHomology M 1 →ₗ[k] Q) :=
  originalCharacterCohomologyQuotientLift Q M ∘ₗ
    ((groupCohomology.H1π (originalLinearCharacterRep Q M)).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm.toLinearMap

/-- On an original cocycle, the cohomological pairing is its descended chain evaluation. -/
theorem originalCharacterFirstPairing_cocycle
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M)) :
    originalCharacterFirstPairing Q M
      (groupCohomology.H1π (originalLinearCharacterRep Q M) c) =
        originalCharacterHomologyEvaluation Q M c := by
  change originalCharacterCohomologyQuotientLift Q M
    (((groupCohomology.H1π (originalLinearCharacterRep Q M)).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm
        ((groupCohomology.H1π (originalLinearCharacterRep Q M)).hom c)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The original cohomology pairing detects zero cohomology classes. -/
theorem originalCharacterFirstPairing_injective :
    Function.Injective (originalCharacterFirstPairing Q M) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    apply (originalCharacterHomologyEvaluation_eq_zero_iff Q M c).mp
    exact (originalCharacterFirstPairing_cocycle Q M c).symm.trans hx

/-- Every functional on original first homology comes from actual first cohomology. -/
theorem originalCharacterFirstPairing_surjective :
    Function.Surjective (originalCharacterFirstPairing Q M) := by
  intro χ
  obtain ⟨c, hc⟩ := originalCharacterHomologyEvaluation_surjective Q M χ
  exact ⟨groupCohomology.H1π (originalLinearCharacterRep Q M) c,
    (originalCharacterFirstPairing_cocycle Q M c).trans hc⟩

/-- Original first cohomology with injective character coefficients is the linear dual of original first homology. -/
def originalCharacterFirstDuality :
    groupCohomology (originalLinearCharacterRep Q M) 1 ≃ₗ[k]
      (groupHomology M 1 →ₗ[k] Q) :=
  LinearEquiv.ofBijective (originalCharacterFirstPairing Q M)
    ⟨originalCharacterFirstPairing_injective Q M,
      originalCharacterFirstPairing_surjective Q M⟩

/-- The duality equivalence evaluates original cocycle and cycle representatives by their literal chain sum. -/
theorem originalCharacterFirstDuality_representatives
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M))
    (z : groupHomology.cycles₁ M) :
    originalCharacterFirstDuality Q M
      (groupCohomology.H1π (originalLinearCharacterRep Q M) c)
      (groupHomology.H1π M z) = originalCharacterChainEvaluation Q M c.val z.val := by
  change originalCharacterFirstPairing Q M
    (groupCohomology.H1π (originalLinearCharacterRep Q M) c) (groupHomology.H1π M z) = _
  rw [originalCharacterFirstPairing_cocycle]
  exact originalCharacterHomologyEvaluation_cycle Q M c z

end
end Dubon2026
