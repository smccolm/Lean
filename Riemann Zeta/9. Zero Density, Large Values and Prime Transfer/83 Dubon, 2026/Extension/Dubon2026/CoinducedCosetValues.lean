import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Original coinduced coefficients evaluated on actual subgroup cosets -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

private theorem coinducedCosetValue_wellDefined
    (f : Rep.coind S.subtype (Rep.res S.subtype A))
    (g h : G) (hgh : QuotientGroup.leftRel S g h) :
    A.ρ g (f.val g⁻¹) = A.ρ h (f.val h⁻¹) := by
  have hs : h⁻¹ * g ∈ S := by
    simpa only [mul_inv_rev, inv_inv] using S.inv_mem (QuotientGroup.leftRel_apply.mp hgh)
  have hf := f.property (⟨h⁻¹ * g, hs⟩ : S) g⁻¹
  change f.val ((h⁻¹ * g) * g⁻¹) = A.ρ (h⁻¹ * g) (f.val g⁻¹) at hf
  simp only [mul_inv_cancel_right] at hf
  rw [hf, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- Untwist the original equivariant function by the original action.
Its value is independent of the representative of the genuine left coset. -/
def coinducedCosetValues :
    Rep.coind S.subtype (Rep.res S.subtype A) →ₗ[k] (G ⧸ S → A) where
  toFun f q := Quotient.liftOn' q (fun g => A.ρ g (f.val g⁻¹))
    (coinducedCosetValue_wellDefined A S f)
  map_add' f h := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H g => exact (A.ρ g).map_add _ _
  map_smul' r f := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H g => exact (A.ρ g).map_smul r _

/-- Evaluation at an original coset retains its literal untwisted value. -/
theorem coinducedCosetValues_mk
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) (g : G) :
    coinducedCosetValues A S f (QuotientGroup.mk g) = A.ρ g (f.val g⁻¹) := by
  rfl

/-- The original coinduced action becomes translation of actual cosets
together with the original coefficient action. -/
theorem coinducedCosetValues_action
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) (h : G) (q : G ⧸ S) :
    coinducedCosetValues A S ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ h f) q =
      A.ρ h (coinducedCosetValues A S f (h⁻¹ • q)) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    change A.ρ g (f.val (g⁻¹ * h)) = A.ρ h (A.ρ (h⁻¹ * g) (f.val (h⁻¹ * g)⁻¹))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv]

end
end Dubon2026
