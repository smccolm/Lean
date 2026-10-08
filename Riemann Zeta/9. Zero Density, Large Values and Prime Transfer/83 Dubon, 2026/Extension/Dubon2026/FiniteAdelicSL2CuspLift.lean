import Dubon2026.FiniteAdeleClassicalIntersection
import Dubon2026.RealAutomorphicLift

/-! # The original cusp function on the real and finite adelic special linear group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The original rational matrix embedded into the real determinant-one group. -/
def rationalSL2ToReal : SL(2, ℚ) →* SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Rat.castHom ℝ)

/-- The original rational matrix embedded into the canonical finite adelic determinant-one group. -/
def rationalSL2ToFinite : SL(2, ℚ) →* SL(2, FiniteAdeleRing ℤ ℚ) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))

/-- Choose the actual rational factor supplied by the proved level strong approximation theorem. -/
def finiteAdelicSL2Representative (N : ℕ) [NeZero N]
    (x : SL(2, FiniteAdeleRing ℤ ℚ)) : SL(2, ℚ) :=
  Classical.choose (rationalSL2_finiteAdeles_gamma0_factorization N x)

/-- The chosen rational representative has an actual right factor in the genuine level subgroup. -/
theorem finiteAdelicSL2Representative_spec (N : ℕ) [NeZero N]
    (x : SL(2, FiniteAdeleRing ℤ ℚ)) :
    ∃ u : finiteAdeleGamma0 N,
      x = rationalSL2ToFinite (finiteAdelicSL2Representative N x) * u.val :=
  Classical.choose_spec (rationalSL2_finiteAdeles_gamma0_factorization N x)

/-- Evaluate the original real-group cusp lift using the actual rational finite-adele factor. -/
def finiteAdelicSL2CuspLift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (x : SL(2, FiniteAdeleRing ℤ ℚ)) : ℂ :=
  realWeightLift k f ((rationalSL2ToReal (finiteAdelicSL2Representative N x))⁻¹ * g)

/-- The exact rational intersection turns finite level membership into original real cusp invariance. -/
theorem rationalSL2_realWeightLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (δ : SL(2, ℚ))
    (hδ : rationalSL2ToFinite δ ∈ finiteAdeleGamma0 N) (g : SL(2, ℝ)) :
    realWeightLift k f (rationalSL2ToReal δ * g) = realWeightLift k f g := by
  obtain ⟨γ, rfl⟩ := (rationalSL2_mem_finiteAdeleGamma0_iff N δ).mp hδ
  apply realWeightLift_cusp_left_invariant
  refine ⟨γ.val, γ.property, ?_⟩
  ext i j
  simp [rationalSL2ToReal, mapGL, Matrix.SpecialLinearGroup.toGL]

/-- The original value is independent of the selected rational factor and has its exact classical formula. -/
theorem finiteAdelicSL2CuspLift_of_decomposition (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, ℝ))
    (x : SL(2, FiniteAdeleRing ℤ ℚ)) (γ : SL(2, ℚ)) (v : finiteAdeleGamma0 N)
    (hx : x = rationalSL2ToFinite γ * v.val) :
    finiteAdelicSL2CuspLift N k f g x = realWeightLift k f ((rationalSL2ToReal γ)⁻¹ * g) := by
  obtain ⟨u, hu⟩ := finiteAdelicSL2Representative_spec N x
  let r := finiteAdelicSL2Representative N x
  have hprod : rationalSL2ToFinite r * u.val = rationalSL2ToFinite γ * v.val :=
    hu.symm.trans hx
  have hδ : rationalSL2ToFinite (r⁻¹ * γ) ∈ finiteAdeleGamma0 N := by
    have heq : rationalSL2ToFinite (r⁻¹ * γ) = u.val * v.val⁻¹ := by
      rw [map_mul, map_inv]
      apply (eq_mul_inv_iff_mul_eq).mpr
      rw [mul_assoc, ← hprod, inv_mul_cancel_left]
    rw [heq]
    exact (finiteAdeleGamma0 N).mul_mem u.property ((finiteAdeleGamma0 N).inv_mem v.property)
  have h := rationalSL2_realWeightLift_level_invariant N f (r⁻¹ * γ) hδ
    ((rationalSL2ToReal γ)⁻¹ * g)
  simpa only [finiteAdelicSL2CuspLift, map_mul, map_inv, mul_assoc,
    mul_inv_cancel_left, r] using h

/-- At finite identity the genuine adelic construction recovers the whole original real-group lift. -/
theorem finiteAdelicSL2CuspLift_one (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, ℝ)) :
    finiteAdelicSL2CuspLift N k f g 1 = realWeightLift k f g := by
  simpa using finiteAdelicSL2CuspLift_of_decomposition N f g 1 1 1 (by simp)

/-- The actual constructed function is left invariant under the diagonal rational determinant-one group. -/
theorem finiteAdelicSL2CuspLift_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (δ : SL(2, ℚ))
    (g : SL(2, ℝ)) (x : SL(2, FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicSL2CuspLift N k f (rationalSL2ToReal δ * g) (rationalSL2ToFinite δ * x) =
      finiteAdelicSL2CuspLift N k f g x := by
  obtain ⟨u, hu⟩ := finiteAdelicSL2Representative_spec N x
  let r := finiteAdelicSL2Representative N x
  have hδx : rationalSL2ToFinite δ * x = rationalSL2ToFinite (δ * r) * u.val := by
    rw [map_mul, mul_assoc, ← hu]
  rw [finiteAdelicSL2CuspLift_of_decomposition N f _ _ (δ * r) u hδx,
    finiteAdelicSL2CuspLift_of_decomposition N f g x r u hu]
  simp only [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- The actual constructed function is right invariant under the genuine finite level subgroup. -/
theorem finiteAdelicSL2CuspLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, ℝ))
    (x : SL(2, FiniteAdeleRing ℤ ℚ)) (v : finiteAdeleGamma0 N) :
    finiteAdelicSL2CuspLift N k f g (x * v.val) = finiteAdelicSL2CuspLift N k f g x := by
  obtain ⟨u, hu⟩ := finiteAdelicSL2Representative_spec N x
  let r := finiteAdelicSL2Representative N x
  have hxv : x * v.val = rationalSL2ToFinite r * (u * v).val := by
    rw [hu, mul_assoc]
    rfl
  rw [finiteAdelicSL2CuspLift_of_decomposition N f g _ r (u * v) hxv,
    finiteAdelicSL2CuspLift_of_decomposition N f g x r u hu]

end
end Dubon2026
