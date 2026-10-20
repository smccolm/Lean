import Dubon2026.SmallLevelAuxiliaryAction
import Dubon2026.AuxiliaryRepresentationModuleEquiv
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Free group-algebra coordinates for the auxiliary level

The inverse in the group coordinate converts weighted right translation to
Mathlib's left regular representation. The existing free representation then
supplies the group-algebra basis required in CHT Lemma 3.3.1.
-/

namespace Dubon2026

noncomputable section

open Module

variable {R D J I W : Type*} [CommRing R] [Group D] [AddCommGroup W] [Module R W]
variable [Finite D] [Finite J] [Finite I]

/-- Basis coordinates, with the inverse group coordinate prescribed by CHT. -/
def auxiliaryRegularCoordinates (b : Basis I R W) :
    (J → D → W) ≃ₗ[R] ((J × I) →₀ D →₀ R) where
  toFun f := (Finsupp.linearEquivFunOnFinite R (D →₀ R) (J × I)).symm
    (fun ji => (Finsupp.linearEquivFunOnFinite R R D).symm
      (fun d => b.equivFun (f ji.1 d⁻¹) ji.2))
  map_add' f g := by
    ext ji d
    simp only [Finsupp.linearEquivFunOnFinite_symm_apply, Pi.add_apply, map_add,
      Finsupp.add_apply]
  map_smul' a f := by
    ext ji d
    simp only [Finsupp.linearEquivFunOnFinite_symm_apply, Pi.smul_apply, map_smul,
      Finsupp.smul_apply, RingHom.id_apply]
  invFun f j d := b.equivFun.symm (fun i => f (j, i) d⁻¹)
  left_inv f := by
    funext j d
    simp only [Finsupp.linearEquivFunOnFinite_symm_apply, inv_inv,
      LinearEquiv.symm_apply_apply]
  right_inv f := by
    ext ji d
    simp only [Finsupp.linearEquivFunOnFinite_symm_apply, inv_inv,
      LinearEquiv.apply_symm_apply]

omit [Finite D] [Finite J] [Finite I] in
/-- The existing free representation acts by the usual left translation on coefficients. -/
theorem auxiliaryFreeRepresentation_apply (d : D)
    (f : (J × I) →₀ D →₀ R) (ji : J × I) (x : D) :
    Representation.free R D (J × I) d f ji x = f ji (d⁻¹ * x) := by
  classical
  change ((Representation.leftRegular R D).finsupp (J × I) d f) ji x = _
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single j a =>
    rw [Representation.finsupp_single]
    by_cases h : ji = j
    · subst ji
      simp only [Finsupp.single_eq_same, Representation.ofMulAction_apply, smul_eq_mul]
    · simp only [Finsupp.single_apply, if_neg (Ne.symm h), Finsupp.zero_apply]

/-- The coordinate equivalence intertwines the actual quotient action with the free representation. -/
theorem auxiliaryRegularCoordinates_intertwines (b : Basis I R W) (d : D) (f : J → D → W) :
    auxiliaryRegularCoordinates (D := D) b (quotientRightTranslation (R := R) d f) =
      Representation.free R D (J × I) d (auxiliaryRegularCoordinates (D := D) b f) := by
  ext ji x
  rw [auxiliaryFreeRepresentation_apply]
  change b.equivFun (f ji.1 (x⁻¹ * d)) ji.2 = b.equivFun (f ji.1 (d⁻¹ * x)⁻¹) ji.2
  rw [mul_inv_rev, inv_inv]

/-- The regular quotient-coordinate module is free over the whole group algebra. -/
theorem auxiliaryRegularModule_free (b : Basis I R W) :
    Module.Free (MonoidAlgebra R D)
      (quotientRightTranslation (R := R) (D := D) (J := J) (W := W)).asModule := by
  letI := Representation.free_asModule_free R D (J × I)
  exact auxiliaryRepresentationModule_free (R := R) (D := D)
    (X := J → D → W) (Y := (J × I) →₀ D →₀ R)
    (quotientRightTranslation (R := R) (D := D) (J := J) (W := W))
    (Representation.free R D (J × I)) (auxiliaryRegularCoordinates b)
    (fun d f => auxiliaryRegularCoordinates_intertwines b d f)

end
end Dubon2026
