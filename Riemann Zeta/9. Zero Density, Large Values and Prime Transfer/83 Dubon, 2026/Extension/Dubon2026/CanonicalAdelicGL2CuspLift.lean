import Dubon2026.CanonicalAdelicGL2Coordinates
import Dubon2026.CanonicalAdelicCuspLift

/-! # The original cusp function on Mathlib's canonical full adelic general linear group -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The original cusp function defined on the actual pinned full adelic general linear group. -/
def canonicalAdelicGL2CuspLift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) : ℂ :=
  fullAdelicGL2CuspLift N k f
    (rationalAdelicGL2RealFiniteEquiv g).1 (rationalAdelicGL2RealFiniteEquiv g).2

/-- The full-adele function agrees exactly with the proved real and finite construction. -/
theorem canonicalAdelicGL2CuspLift_coordinates (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ) (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f (rationalAdelicGL2RealFiniteEquiv.symm (g, x)) =
      fullAdelicGL2CuspLift N k f g x := by
  simp only [canonicalAdelicGL2CuspLift, MulEquiv.apply_symm_apply]

/-- The literal original function is continuous on the canonical full adelic group. -/
theorem canonicalAdelicGL2CuspLift_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Continuous (canonicalAdelicGL2CuspLift N k f) :=
  (fullAdelicGL2CuspLift_continuous N f).comp rationalAdelicGL2RealFiniteEquiv_continuous

/-- The original full-adele function is invariant under the actual principal rational group. -/
theorem canonicalAdelicGL2CuspLift_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) =
        canonicalAdelicGL2CuspLift N k f g := by
  unfold canonicalAdelicGL2CuspLift
  rw [map_mul, rationalAdelicGL2RealFiniteEquiv_rational]
  exact fullAdelicGL2CuspLift_rational_invariant N f γ _ _

/-- The archimedean restriction recovers the original unitary positive-real cusp function. -/
theorem canonicalAdelicGL2CuspLift_real_restriction (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺) :
    canonicalAdelicGL2CuspLift N k f (rationalAdelicGL2RealFiniteEquiv.symm (g.val, 1)) =
      realPositiveUnitaryLift k f g := by
  rw [canonicalAdelicGL2CuspLift_coordinates, fullAdelicGL2CuspLift_one]

/-- The full-adele construction is right invariant under the genuine finite level subgroup. -/
theorem canonicalAdelicGL2CuspLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) (u : finiteAdeleGL2Gamma0 N) :
    canonicalAdelicGL2CuspLift N k f (g * rationalAdelicGL2RealFiniteEquiv.symm (1, u.val)) =
      canonicalAdelicGL2CuspLift N k f g := by
  unfold canonicalAdelicGL2CuspLift
  rw [map_mul, MulEquiv.apply_symm_apply]
  simpa only [Prod.fst_mul, Prod.snd_mul, mul_one] using
    fullAdelicGL2CuspLift_level_invariant N f
      (rationalAdelicGL2RealFiniteEquiv g).1 (rationalAdelicGL2RealFiniteEquiv g).2 u

/-- The actual canonical adelic lift retains the original classical cusp form injectively. -/
theorem canonicalAdelicGL2CuspLift_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fun f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k =>
      canonicalAdelicGL2CuspLift N k f) := by
  intro f h he
  apply fullAdelicGL2CuspLift_injective N k
  funext g x
  have ht := congrFun he (rationalAdelicGL2RealFiniteEquiv.symm (g, x))
  simpa only [canonicalAdelicGL2CuspLift_coordinates] using ht

/-- On the actual determinant-one matrices the full GL2 construction is the original SL2 lift. -/
theorem fullAdelicGL2CuspLift_toGL (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : SL(2, ℝ)) (x : SL(2, FiniteAdeleRing ℤ ℚ)) :
    fullAdelicGL2CuspLift N k f (toGL g) (toGL x) = finiteAdelicSL2CuspLift N k f g x := by
  obtain ⟨u, hu⟩ := finiteAdelicSL2Representative_spec N x
  let r := finiteAdelicSL2Representative N x
  let v : finiteAdeleGL2Gamma0 N := ⟨toGL u.val, finiteAdeleGamma0_toGL_mem N _ u.property⟩
  have hf : toGL x = rationalPositiveGL2ToFinite (toGLPos r) * v.val := by
    have he : rationalPositiveGL2ToFinite (toGLPos r) = toGL (rationalSL2ToFinite r) := by
      apply Units.ext
      rfl
    rw [he]
    change toGL x = toGL (rationalSL2ToFinite r) * toGL u.val
    rw [← map_mul, ← hu]
  have hr : rationalPositiveGL2ToReal (toGLPos r) = toGLPos (rationalSL2ToReal r) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [show toGL g = (toGLPos g).val from rfl, fullAdelicGL2CuspLift_positive,
    positiveAdelicGL2CuspLift_of_decomposition N f _ _ (toGLPos r) v hf, hr,
    ← map_inv, ← map_mul, realPositiveUnitaryLift_toGLPos,
    finiteAdelicSL2CuspLift_of_decomposition N f g x r u hu]

/-- The full canonical GL2 cusp function extends the actual previously constructed canonical SL2 function exactly. -/
theorem canonicalAdelicGL2CuspLift_toGL (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, AdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f (toGL g) = canonicalAdelicCuspLift N k f g := by
  unfold canonicalAdelicGL2CuspLift canonicalAdelicCuspLift
  rw [rationalAdelicGL2RealFiniteEquiv_toGL]
  exact fullAdelicGL2CuspLift_toGL N f _ _

end
end Dubon2026
