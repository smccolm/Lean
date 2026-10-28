import Dubon2026.SourceCurveCorrespondenceRamification
import Dubon2026.SourceGammaOneHeckeConstantPlaces
import Dubon2026.SourceGammaOneDivisorConorm

/-! DUB17/18 -> actual arithmetic Gamma1 Tate/Hecke comparison ->
restriction and ramification on the actual correspondence curve.
The proved place extensions preserve exact orders. These naturality
lemmas retain explicit finite-map and commuting-square inputs, which
the actual alpha and beta maps discharge in the Picard consumer. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ) [NeZero M] [NeZero d]
variable (φ : functionFieldOver (Gamma1 M) Qbar →ₐ[Qbar] functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar)
variable (ψ : functionFieldOver (Gamma1 M) ℂ →ₐ[ℂ] functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ)
variable (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
variable (hcomm : ∀ x, HeckeConstantField.fieldMap M d (φ x) = ψ (fieldMap M x))
include hcomm

theorem restrictAlong_heckeLiftPlace (w : Place Qbar (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar)) :
    Place.restrictAlong ψ hψ (HeckeConstantField.liftPlace M d w) =
      liftPlace M (Place.restrictAlong φ hφ w) := by
  apply liftPlace_unique M
  exact Place.comap_restrictAlong_eq_of_commute φ ψ hφ hψ (fieldMap M) (HeckeConstantField.fieldMap M d)
    w (HeckeConstantField.liftPlace M d w) (HeckeConstantField.liftPlace_comap M d w) hcomm

theorem ramificationAlong_heckeLiftPlace (w : Place Qbar (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar)) :
    Place.ramificationAlong ψ hψ (HeckeConstantField.liftPlace M d w) = Place.ramificationAlong φ hφ w := by
  have h := Place.ord_restrictAlong ψ hψ (HeckeConstantField.liftPlace M d w)
    (fieldMap M (Place.restrictAlong φ hφ w).uniformizer)
  rw [restrictAlong_heckeLiftPlace M d φ ψ hφ hψ hcomm,
    ord_liftPlace, Place.ord_uniformizer, one_mul] at h
  rw [← hcomm, HeckeConstantField.ord_liftPlace] at h
  exact h.symm

theorem restrictAlong_ne_liftPlace_of_ne_hecke
    {w : Place ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ)} (hoff : ∀ v, w ≠ HeckeConstantField.liftPlace M d v)
    (v : Place Qbar (functionFieldOver (Gamma1 M) Qbar)) :
    Place.restrictAlong ψ hψ w ≠ liftPlace M v := by
  intro hv
  have h := Place.ord_restrictAlong ψ hψ w (fieldMap M v.uniformizer)
  rw [hv, ord_liftPlace, Place.ord_uniformizer, one_mul,
    ← hcomm, HeckeConstantField.ord_phi_of_forall_ne M d hoff] at h
  have hpos := Place.ramificationAlong_pos ψ hψ w
  omega

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
