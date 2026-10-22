import Dubon2026.SourceOriginalHeckeUpperEquiv
import Dubon2026.SourceOriginalHeckeAnalyticRamification
import Dubon2026.SourceOriginalAnalyticOrbitSeparation
import Dubon2026.SourceOriginalAnalyticRamification

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
fiber multiplicities. The actual raised-level places are classified by
orbits of the upper congruence subgroup after dilation. Their stabilizer
cardinalities give the exact normalized ramification ratio.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
open scoped MatrixGroups
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [NeZero N] in
theorem originalHecke_stabilizer_card (w : ℍ) :
    Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 (N * ℓ)) w) =
      Nat.card (MulAction.stabilizer (heckeUpperSubgroup N ℓ) (levelRaiseMatrix ℓ • w)) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (originalHeckeUpperEquiv N ℓ) ?_)
  intro g
  change g.val.val • (levelRaiseMatrix ℓ • w) = levelRaiseMatrix ℓ • w ↔
    (originalHeckeUpperToRaised N ℓ g).val • w = w
  rw [← originalHeckeUpperToRaised_smul, smul_left_cancel_iff]

theorem originalAnalyticPlace_eq_iff_heckeUpper_orbit (w w₀ : ℍ) :
    originalAnalyticPlace (N * ℓ) w = originalAnalyticPlace (N * ℓ) w₀ ↔
      levelRaiseMatrix ℓ • w ∈
        MulAction.orbit (heckeUpperSubgroup N ℓ) (levelRaiseMatrix ℓ • w₀) := by
  rw [originalAnalyticPlace_eq_iff_gamma0_orbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, rfl⟩ := (originalHeckeUpperEquiv N ℓ).surjective γ
    refine ⟨g⁻¹, ?_⟩
    rw [inv_smul_eq_iff]
    change levelRaiseMatrix ℓ • w₀ = g.val.val • (levelRaiseMatrix ℓ • w)
    rw [← originalHeckeUpperToRaised_smul]
    exact congrArg (levelRaiseMatrix ℓ • ·) hγ.symm
  · rintro ⟨g, hg⟩
    refine ⟨originalHeckeUpperToRaised N ℓ g⁻¹, ?_⟩
    apply (MulAction.injective (levelRaiseMatrix ℓ))
    dsimp only
    rw [originalHeckeUpperToRaised_smul]
    change g⁻¹ • (levelRaiseMatrix ℓ • w) = levelRaiseMatrix ℓ • w₀
    rw [← hg, inv_smul_smul]

theorem originalHeckeBeta_stabilizer_ramification (w : ℍ) :
    (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N)
        (levelRaiseMatrix ℓ • w)) : ℤ) =
      (Nat.card (MulAction.stabilizer (heckeUpperSubgroup N ℓ)
        (levelRaiseMatrix ℓ • w)) : ℤ) *
      Place.ramificationAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
        (originalAnalyticPlace (N * ℓ) w) := by
  rw [← originalHecke_stabilizer_card N ℓ,
    ← original_two_mul_ramification_eq_stabilizer_card N,
    ← original_two_mul_ramification_eq_stabilizer_card (N * ℓ)]
  push_cast
  rw [originalHeckeBeta_analytic_ramification N ℓ]
  ring

end
end Dubon2026.SourceFunctionField
