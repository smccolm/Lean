import Dubon2026.PositiveRationalGL2Intersection
import Dubon2026.RealPositiveUnitaryLift

/-! # The original unitary cusp function on positive real and finite adelic GL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The actual positive rational matrix maps to the original positive real group. -/
def rationalPositiveGL2ToReal : GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ where
  toFun γ := ⟨Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ.val, by
    change 0 < (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ.val)).val
    rw [Matrix.GeneralLinearGroup.map_det]
    change 0 < ((Matrix.GeneralLinearGroup.det γ.val).val : ℝ)
    exact_mod_cast γ.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' γ δ := by apply Subtype.ext; exact map_mul _ γ.val δ.val

/-- The actual positive rational matrix maps to the canonical finite adelic general-linear group. -/
def rationalPositiveGL2ToFinite :
    GL(2, ℚ)⁺ →* Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))).comp
    (Matrix.GLPos (Fin 2) ℚ).subtype

/-- Choose the actual rational factor supplied by the proved level strong approximation theorem. -/
def positiveAdelicGL2Representative (N : ℕ) [NeZero N]
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : GL(2, ℚ)⁺ :=
  Classical.choose (rationalGL2_finiteAdeles_gamma0_factorization N x)

/-- The chosen rational representative has an actual right factor in the genuine level subgroup. -/
theorem positiveAdelicGL2Representative_spec (N : ℕ) [NeZero N]
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∃ u : finiteAdeleGL2Gamma0 N,
      x = rationalPositiveGL2ToFinite (positiveAdelicGL2Representative N x) * u.val :=
  Classical.choose_spec (rationalGL2_finiteAdeles_gamma0_factorization N x)

/-- Evaluate the original positive-real unitary cusp lift using the actual rational finite-adele factor. -/
def positiveAdelicGL2CuspLift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : GL(2, ℝ)⁺) (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : ℂ :=
  realPositiveUnitaryLift k f ((rationalPositiveGL2ToReal (positiveAdelicGL2Representative N x))⁻¹ * g)

/-- The exact rational intersection turns finite level membership into original real cusp invariance. -/
theorem rationalPositiveGL2_realLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (δ : GL(2, ℚ)⁺)
    (hδ : rationalPositiveGL2ToFinite δ ∈ finiteAdeleGL2Gamma0 N) (g : GL(2, ℝ)⁺) :
    realPositiveUnitaryLift k f (rationalPositiveGL2ToReal δ * g) = realPositiveUnitaryLift k f g := by
  obtain ⟨γ, hγ⟩ := (positiveRationalGL2_mem_finiteAdeleGamma0_iff N δ).mp hδ
  have he : rationalPositiveGL2ToReal δ = toGLPos (integralToRealSL γ.val) := by
    apply Subtype.ext
    change Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ.val = _
    rw [← hγ]
    apply Units.ext
    funext i j
    exact map_intCast (Rat.castHom ℝ) (γ.val i j)
  rw [he]
  exact realPositiveUnitaryLift_arithmetic f γ.val γ.property g

/-- The original value is independent of the selected rational factor and has its exact classical formula. -/
theorem positiveAdelicGL2CuspLift_of_decomposition (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (γ : GL(2, ℚ)⁺) (v : finiteAdeleGL2Gamma0 N)
    (hx : x = rationalPositiveGL2ToFinite γ * v.val) :
    positiveAdelicGL2CuspLift N k f g x = realPositiveUnitaryLift k f ((rationalPositiveGL2ToReal γ)⁻¹ * g) := by
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N x
  let r := positiveAdelicGL2Representative N x
  have hprod : rationalPositiveGL2ToFinite r * u.val = rationalPositiveGL2ToFinite γ * v.val :=
    hu.symm.trans hx
  have hδ : rationalPositiveGL2ToFinite (r⁻¹ * γ) ∈ finiteAdeleGL2Gamma0 N := by
    have heq : rationalPositiveGL2ToFinite (r⁻¹ * γ) = u.val * v.val⁻¹ := by
      rw [map_mul, map_inv]
      apply (eq_mul_inv_iff_mul_eq).mpr
      rw [mul_assoc, ← hprod, inv_mul_cancel_left]
    rw [heq]
    exact (finiteAdeleGL2Gamma0 N).mul_mem u.property ((finiteAdeleGL2Gamma0 N).inv_mem v.property)
  have h := rationalPositiveGL2_realLift_level_invariant N f (r⁻¹ * γ) hδ
    ((rationalPositiveGL2ToReal γ)⁻¹ * g)
  simpa only [positiveAdelicGL2CuspLift, map_mul, map_inv, mul_assoc,
    mul_inv_cancel_left, r] using h

/-- At finite identity the genuine adelic construction recovers the whole original real-group lift. -/
theorem positiveAdelicGL2CuspLift_one (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺) :
    positiveAdelicGL2CuspLift N k f g 1 = realPositiveUnitaryLift k f g := by
  simpa using positiveAdelicGL2CuspLift_of_decomposition N f g 1 1 1 (by simp)

/-- The actual constructed function is left invariant under the diagonal rational general-linear group. -/
theorem positiveAdelicGL2CuspLift_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (δ : GL(2, ℚ)⁺)
    (g : GL(2, ℝ)⁺) (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    positiveAdelicGL2CuspLift N k f (rationalPositiveGL2ToReal δ * g) (rationalPositiveGL2ToFinite δ * x) =
      positiveAdelicGL2CuspLift N k f g x := by
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N x
  let r := positiveAdelicGL2Representative N x
  have hδx : rationalPositiveGL2ToFinite δ * x = rationalPositiveGL2ToFinite (δ * r) * u.val := by
    rw [map_mul, mul_assoc, ← hu]
  rw [positiveAdelicGL2CuspLift_of_decomposition N f _ _ (δ * r) u hδx,
    positiveAdelicGL2CuspLift_of_decomposition N f g x r u hu]
  simp only [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- The actual constructed function is right invariant under the genuine finite level subgroup. -/
theorem positiveAdelicGL2CuspLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : finiteAdeleGL2Gamma0 N) :
    positiveAdelicGL2CuspLift N k f g (x * v.val) = positiveAdelicGL2CuspLift N k f g x := by
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N x
  let r := positiveAdelicGL2Representative N x
  have hxv : x * v.val = rationalPositiveGL2ToFinite r * (u * v).val := by
    rw [hu, mul_assoc]
    rfl
  rw [positiveAdelicGL2CuspLift_of_decomposition N f g _ r (u * v) hxv,
    positiveAdelicGL2CuspLift_of_decomposition N f g x r u hu]

end
end Dubon2026
