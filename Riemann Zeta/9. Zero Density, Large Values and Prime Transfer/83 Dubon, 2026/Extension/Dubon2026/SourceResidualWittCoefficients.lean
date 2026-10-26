import Dubon2026.SourceWittResidueLift
import Mathlib.FieldTheory.Finite.Basic

/-! DUB-17/18 -> arithmetic automorphy -> the actual finite residual
deformation problem. Reuse the proved Witt residue map and native complete
discrete valuation ring to realize the constructed finite coefficient
field as the residue field of a characteristic-zero coefficient ring. -/
namespace Dubon2026
noncomputable section
open IsLocalRing

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K p]

/-- The actual Witt residue field is exactly the original finite field. -/
def sourceResidualWittResidueEquiv : ResidueField (WittVector p K) ≃+* K :=
  (RingEquiv.ofBijective
    (SourceWittLift.residueMap p K (RingHom.id (WittVector p K)))
    ⟨(RingHom.injective _), by
      intro x
      obtain ⟨w, rfl⟩ := residue_surjective x
      exact ⟨WittVector.constantCoeff w,
        SourceWittLift.residueMap_constantCoeff p K (RingHom.id _) w⟩⟩).symm

theorem sourceResidualWittResidueEquiv_residue (w : WittVector p K) :
    sourceResidualWittResidueEquiv p K (residue (WittVector p K) w) =
      WittVector.constantCoeff w := by
  apply (sourceResidualWittResidueEquiv p K).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (SourceWittLift.residueMap_constantCoeff p K (RingHom.id _) w).symm

theorem sourceResidualWittCoefficient_localData :
    CharZero (WittVector p K) ∧
    IsNoetherianRing (WittVector p K) ∧
    IsAdicComplete (maximalIdeal (WittVector p K)) (WittVector p K) ∧
    Finite (ResidueField (WittVector p K)) ∧
    CharP (ResidueField (WittVector p K)) p := by
  have hc : Function.Surjective (WittVector.constantCoeff : WittVector p K →+* K) := by
    intro x
    exact ⟨WittVector.teichmuller p x, by
      rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  have hm : maximalIdeal (WittVector p K) =
      Ideal.span ({(p : WittVector p K)} : Set _) := by
    rw [← IsLocalRing.ker_eq_maximalIdeal (WittVector.constantCoeff : WittVector p K →+* K) hc,
      WittVector.ker_constantCoeff]
  refine ⟨SourceWittLift.witt_charZero p K, inferInstance, ?_, ?_, ?_⟩
  · rw [hm]
    infer_instance
  · exact Finite.of_injective (sourceResidualWittResidueEquiv p K)
      (sourceResidualWittResidueEquiv p K).injective
  · constructor
    intro n
    rw [← (sourceResidualWittResidueEquiv p K).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K p n

end
end Dubon2026
