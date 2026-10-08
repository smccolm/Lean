import Dubon2026.RealPositiveNormalize

/-! # The original real cusp lift with the genuine unitary GL2 normalization -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The actual unitary positive-real GL2 lift obtained from the original normalized SL2 lift. -/
def realPositiveUnitaryLift (k : ℤ) (f : ℍ → ℂ) (g : GL(2, ℝ)⁺) : ℂ :=
  realWeightLift k f (realPositiveNormalize g)

/-- The literal formula has the genuine square-root determinant factor to the original weight. -/
theorem realPositiveUnitaryLift_apply (k : ℤ) (f : ℍ → ℂ) (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f g =
      (realPositiveDetRoot g : ℂ) ^ k * f (g.val • I) * denom g.val I ^ (-k) := by
  rw [realPositiveUnitaryLift, realWeightLift_apply, realPositiveNormalize_smul,
    realPositiveNormalize_denom, mul_zpow, inv_zpow, zpow_neg, inv_inv]
  ring

/-- The genuine positive-real lift retains the original determinant-one cusp function exactly. -/
theorem realPositiveUnitaryLift_toGLPos (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    realPositiveUnitaryLift k f (toGLPos g) = realWeightLift k f g := by
  rw [realPositiveUnitaryLift, realPositiveNormalize_toGLPos]

/-- The exact correction between the pinned slash convention and the genuine unitary normalization. -/
theorem realPositiveUnitaryLift_slash_correction (k : ℤ) (f : ℍ → ℂ) (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f g =
      (realPositiveDetRoot g : ℂ) ^ (2 - k) * (f ∣[k] g.val) I := by
  have hσ : UpperHalfPlane.σ g.val = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    exact if_pos (show 0 < g.val.det.val from g.property)
  have hr : (realPositiveDetRoot g : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realPositiveDetRoot_pos g).ne'
  have hd : (g.val.det.val : ℂ) = (realPositiveDetRoot g : ℂ) ^ (2 : ℤ) := by
    exact_mod_cast (realPositiveDetRoot_sq g).symm
  rw [realPositiveUnitaryLift_apply, ModularForm.slash_apply, hσ,
    ContinuousAlgEquiv.refl_apply, abs_of_pos g.property, hd, ← zpow_mul]
  have he : (2 - k) + 2 * (k - 1) = k := by omega
  have hp : (realPositiveDetRoot g : ℂ) ^ (2 - k) *
      (realPositiveDetRoot g : ℂ) ^ (2 * (k - 1)) = (realPositiveDetRoot g : ℂ) ^ k := by
    rw [← zpow_add₀ hr, he]
  rw [← hp]
  ring

/-- Actual continuity of the original classical function gives continuity of its unitary GL2 lift. -/
theorem realPositiveUnitaryLift_continuous (k : ℤ) {f : ℍ → ℂ} (hf : Continuous f) :
    Continuous (realPositiveUnitaryLift k f) :=
  (realWeightLift_continuous k hf).comp realPositiveNormalize_continuous

/-- The actual completed original Hilbert representation extends to the positive real GL2 group. -/
def realPositiveHilbertRepresentation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Representation ℂ GL(2, ℝ)⁺ (RealProjectiveHilbert f) :=
  (realProjectiveHilbertRepresentation f).comp
    ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp realPositiveNormalize)

/-- The actual positive-real extension still acts strongly continuously on every original completed vector. -/
theorem realPositiveHilbertRepresentation_stronglyContinuous {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (v : RealProjectiveHilbert f) :
    Continuous (fun g : GL(2, ℝ)⁺ => realPositiveHilbertRepresentation f g v) :=
  (realProjectiveHilbertRepresentation_stronglyContinuous f v).comp
    (QuotientGroup.continuous_mk.comp realPositiveNormalize_continuous)

/-- The genuine completed extension preserves the original Hilbert inner product. -/
theorem realPositiveHilbertRepresentation_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (g : GL(2, ℝ)⁺)
    (v w : RealProjectiveHilbert f) :
    inner ℂ (realPositiveHilbertRepresentation f g v) (realPositiveHilbertRepresentation f g w) =
      inner ℂ v w :=
  realProjectiveHilbertRepresentation_inner f (QuotientGroup.mk (realPositiveNormalize g)) v w

/-- The genuine unitary positive-real lift still determines its entire original classical function. -/
theorem realPositiveUnitaryLift_injective (k : ℤ) : Function.Injective (realPositiveUnitaryLift k) := by
  intro f f' he
  apply realWeightLift_injective k
  funext g
  simpa only [realPositiveUnitaryLift_toGLPos] using congrFun he (toGLPos g)

/-- The original actual Petersson density is retained with its exact unitary positive-real normalization. -/
theorem realPositiveUnitaryLift_pairing (k : ℤ) (f f' : ℍ → ℂ) (g : GL(2, ℝ)⁺) :
    starRingEnd ℂ (realPositiveUnitaryLift k f g) * realPositiveUnitaryLift k f' g =
      petersson k f f' (g.val • I) := by
  rw [realPositiveUnitaryLift, realPositiveUnitaryLift, realWeightLift_pairing,
    realPositiveNormalize_smul]

/-- Original arithmetic left invariance survives the genuine positive-real unitary normalization. -/
theorem realPositiveUnitaryLift_arithmetic {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 Q) (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f (toGLPos (integralToRealSL γ) * g) =
      realPositiveUnitaryLift k f g := by
  rw [realPositiveUnitaryLift, realPositiveUnitaryLift, map_mul, realPositiveNormalize_toGLPos]
  apply realWeightLift_cusp_left_invariant
  rw [integralToRealSL_mapGL]
  exact ⟨γ, hγ, rfl⟩

/-- Restriction of the actual positive-real Hilbert representation is exactly the original projective action. -/
theorem realPositiveHilbertRepresentation_toGLPos {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (g : SL(2, ℝ))
    (v : RealProjectiveHilbert f) :
    realPositiveHilbertRepresentation f (toGLPos g) v =
      realProjectiveHilbertRepresentation f (QuotientGroup.mk g) v := by
  change realProjectiveHilbertRepresentation f
    (QuotientGroup.mk (realPositiveNormalize (toGLPos g))) v = _
  rw [realPositiveNormalize_toGLPos]

end
end Dubon2026
