import Dubon2026.SourceLaurentEuler
import Mathlib.RingTheory.Kaehler.Basic

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form dimension lower bound -> regular differential realization
with injective q-expansion. This selected foundation constructs the literal
q d/dq derivation and its map on Kaehler differentials. The original-field application is assembled in
SourceOriginalDifferentialInjectivity with transcendence and separability
proved. Regularity, geometric genus and cusp-form realization remain required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_HeckeDifferential.lean, QExpansion section.
-/
namespace Dubon2026.SourceDifferential
noncomputable section
open HahnSeries KaehlerDifferential

section QExpansion

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

instance instScalarTower : IsScalarTower L F (LaurentSeries L) :=
  ⟨fun c f x => by
    show ((c • f : F) : LaurentSeries L) * x = c • ((f : LaurentSeries L) * x)
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_apply_alt,
      ← C_apply, mul_assoc, C_mul_eq_smul]⟩

/-- Restrict the literal q d/dq derivation to a Laurent-series intermediate field. -/
def qEulerOn : Derivation L F (LaurentSeries L) :=
  (qEuler L).compAlgebraMap F

@[simp] theorem qEulerOn_apply (x : F) : qEulerOn F x = qEuler L (x : LaurentSeries L) := rfl

/-- The universal differential map induced by the literal q d/dq derivation. -/
def diffQExp : Ω[F⁄L] →ₗ[F] LaurentSeries L :=
  (qEulerOn F).liftKaehlerDifferential

@[simp] theorem diffQExp_D (x : F) : diffQExp F (D L F x) = qEuler L (x : LaurentSeries L) :=
  (qEulerOn F).liftKaehlerDifferential_comp_D x

theorem diffQExp_smul_D (f x : F) :
    diffQExp F (f • D L F x) = (f : LaurentSeries L) * qEuler L (x : LaurentSeries L) := by
  rw [map_smul, diffQExp_D]
  rfl

end QExpansion

end
end Dubon2026.SourceDifferential
