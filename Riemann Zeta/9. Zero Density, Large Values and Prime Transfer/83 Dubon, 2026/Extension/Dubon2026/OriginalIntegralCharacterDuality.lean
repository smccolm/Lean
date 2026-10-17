import Dubon2026.OriginalRationalHomCohomology

/-! # Integral degree-two duality through the actual character sequence

The literal integer/rational/rational-circle sequence supplies the
connecting equivalence. Rational cohomology vanishing and ordinary
character duality are both derived. This is DUB-17's integral duality
input before the still-required normalized fundamental-class comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
variable [Module.Projective ℤ M]

/-- The actual integer/rational/character connecting map is an isomorphism in the required degrees. -/
theorem originalIntegerCharacterConnecting_isIso :
    IsIso (groupCohomology.δ (originalRationalCharacterInternalHom_shortExact G M) 1 2 rfl) := by
  obtain ⟨h₁, h₂⟩ := originalRationalHom_first_second_zero M
  exact groupCohomology.isIso_δ_of_isZero
    (originalRationalCharacterInternalHom_shortExact G M) 1 h₁ h₂

/-- The literal connecting map from character-valued H1 to integral-dual H2, as a linear equivalence. -/
def originalIntegerCharacterConnecting :
    groupCohomology (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) 1 ≃ₗ[ℤ]
      groupCohomology (originalLinearCharacterRep ℤ M) 2 := by
  letI := originalIntegerCharacterConnecting_isIso M
  exact (asIso (groupCohomology.δ
    (originalRationalCharacterInternalHom_shortExact G M) 1 2 rfl)).toLinearEquiv

/-- The connecting equivalence is the actual long-exact-sequence boundary map. -/
theorem originalIntegerCharacterConnecting_apply
    (x : groupCohomology (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) 1) :
    originalIntegerCharacterConnecting M x =
      groupCohomology.δ (originalRationalCharacterInternalHom_shortExact G M) 1 2 rfl x := rfl

/-- Integral-dual H2 is the rational-circle character module of original H1, through the actual connecting map. -/
def originalIntegralCharacterDuality :
    groupCohomology (originalLinearCharacterRep ℤ M) 2 ≃ₗ[ℤ]
      (groupHomology M 1 →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  (originalIntegerCharacterConnecting M).symm.trans (originalRationalCharacterFirstDuality M)

/-- The integral duality formula on a class obtained by the actual connecting map retains the original chain evaluation. -/
theorem originalIntegralCharacterDuality_connecting_representatives
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep (AddCircle (1 : ℚ)) M))
    (z : groupHomology.cycles₁ M) :
    originalIntegralCharacterDuality M
      (originalIntegerCharacterConnecting M
        (groupCohomology.H1π (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) c))
      (groupHomology.H1π M z) =
        originalCharacterChainEvaluation (AddCircle (1 : ℚ)) M c.val z.val := by
  change originalRationalCharacterFirstDuality M
    ((originalIntegerCharacterConnecting M).symm
      (originalIntegerCharacterConnecting M
        (groupCohomology.H1π (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) c)))
      (groupHomology.H1π M z) = _
  rw [LinearEquiv.symm_apply_apply]
  exact originalRationalCharacterFirstDuality_representatives M c z

/-- The integral pairing separates original first homology classes without a perfectness hypothesis. -/
theorem originalIntegralCharacterDuality_right_nondegenerate
    (x : groupHomology M 1) (hx : ∀ c, originalIntegralCharacterDuality M c x = 0) : x = 0 := by
  apply originalRationalCharacterFirstDuality_right_nondegenerate M x
  intro c
  have he := hx (originalIntegerCharacterConnecting M c)
  change originalRationalCharacterFirstDuality M
    ((originalIntegerCharacterConnecting M).symm (originalIntegerCharacterConnecting M c)) x = 0 at he
  simpa only [LinearEquiv.symm_apply_apply] using he

end
end Dubon2026
