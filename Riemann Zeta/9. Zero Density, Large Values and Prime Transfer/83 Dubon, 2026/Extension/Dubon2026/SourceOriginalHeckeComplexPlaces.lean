import Dubon2026.SourceCurveCorrespondenceRamification
import Dubon2026.SourceOriginalHeckeFieldNaturality
import Dubon2026.SourceOriginalDivisorConorm

/-! DUB-17/18 -> original Tate Hecke comparison -> the actual Qbar-to-complex
Picard map. Unique extension of original places and exact preservation of
orders identify restrictions and ramification under the two degeneracy maps.
Positivity of ramification excludes an arithmetic restriction for any complex
place outside the original arithmetic image.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N M : ℕ) [NeZero N] [NeZero M]
variable (φ : modularFunctionFieldOver N Qbar →ₐ[Qbar] modularFunctionFieldOver M Qbar)
variable (ψ : modularFunctionFieldOver N ℂ →ₐ[ℂ] modularFunctionFieldOver M ℂ)
variable (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
variable (hcomm : ∀ x, fieldMap M (φ x) = ψ (fieldMap N x))
include hcomm

theorem restrictAlong_liftPlace (w : Place Qbar (modularFunctionFieldOver M Qbar)) :
    Place.restrictAlong ψ hψ (liftPlace M w) =
      liftPlace N (Place.restrictAlong φ hφ w) := by
  apply liftPlace_unique N
  exact Place.comap_restrictAlong_eq_of_commute φ ψ hφ hψ (fieldMap N) (fieldMap M)
    w (liftPlace M w) (liftPlace_comap M w) hcomm

theorem ramificationAlong_liftPlace (w : Place Qbar (modularFunctionFieldOver M Qbar)) :
    Place.ramificationAlong ψ hψ (liftPlace M w) = Place.ramificationAlong φ hφ w := by
  have h := Place.ord_restrictAlong ψ hψ (liftPlace M w)
    (fieldMap N (Place.restrictAlong φ hφ w).uniformizer)
  rw [restrictAlong_liftPlace N M φ ψ hφ hψ hcomm,
    ord_liftPlace, Place.ord_uniformizer, one_mul] at h
  rw [← hcomm, ord_liftPlace] at h
  exact h.symm

theorem restrictAlong_ne_liftPlace_of_ne
    {w : Place ℂ (modularFunctionFieldOver M ℂ)} (hoff : ∀ v, w ≠ liftPlace M v)
    (v : Place Qbar (modularFunctionFieldOver N Qbar)) :
    Place.restrictAlong ψ hψ w ≠ liftPlace N v := by
  intro hv
  have h := Place.ord_restrictAlong ψ hψ w (fieldMap N v.uniformizer)
  rw [hv, ord_liftPlace, Place.ord_uniformizer, one_mul,
    ← hcomm, ord_phi_of_forall_ne M hoff] at h
  have hpos := Place.ramificationAlong_pos ψ hψ w
  omega

end
end Dubon2026.SourceFunctionField.OriginalConstantField
