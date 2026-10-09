import Dubon2026.AdelicCyclicLevelDescent

/-! # Exact full-adelic reconstruction from original rational, central and level invariance -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- Actual rational left invariance in the literal real and finite coordinates. -/
theorem adelicFunction_rational_coordinates (v : RationalAdelicGL2 → ℂ)
    (hv : ∀ γ : GeneralLinearGroup (Fin 2) ℚ, ∀ g,
      v (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) = v g)
    (γ : GeneralLinearGroup (Fin 2) ℚ) (g : GeneralLinearGroup (Fin 2) ℝ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    v (rationalAdelicGL2RealFiniteEquiv.symm (rationalGL2ToReal γ * g, rationalGL2ToFinite γ * a)) =
      v (rationalAdelicGL2RealFiniteEquiv.symm (g, a)) := by
  have he : rationalAdelicGL2RealFiniteEquiv.symm (rationalGL2ToReal γ * g, rationalGL2ToFinite γ * a) =
      GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ *
        rationalAdelicGL2RealFiniteEquiv.symm (g, a) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [MulEquiv.apply_symm_apply, map_mul, rationalAdelicGL2RealFiniteEquiv_rational,
      MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  exact hv γ _

/-- Genuine trivial scalar invariance identifies the positive real value with the actual determinant-one normalization. -/
theorem adelicFunction_real_normalize (v : RationalAdelicGL2 → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (g : GL(2, ℝ)⁺) : v (adelicRealGL2Embedding g.val) =
      v (adelicRealSL2Embedding (realPositiveNormalize g)) := by
  have h := adelicFunction_scalar_pair v hv
    (Units.mk0 (realPositiveDetRoot g) (realPositiveDetRoot_pos g).ne') 1
    (toGL (realPositiveNormalize g)) 1
  simpa only [realPositiveNormalize_factor, map_one, one_mul] using h

/-- Actual level right invariance removes precisely the original finite level coordinate. -/
theorem adelicFunction_level_coordinates (N : ℕ) (v : RationalAdelicGL2 → ℂ)
    (hv : ∀ a : finiteAdeleGL2Gamma0 N, ∀ g,
      v (g * rationalAdelicFiniteGL2Embedding a.val) = v g)
    (g : GeneralLinearGroup (Fin 2) ℝ) (a : finiteAdeleGL2Gamma0 N) :
    v (rationalAdelicGL2RealFiniteEquiv.symm (g, a.val)) = v (adelicRealGL2Embedding g) := by
  have he : rationalAdelicGL2RealFiniteEquiv.symm (g, a.val) =
      adelicRealGL2Embedding g * rationalAdelicFiniteGL2Embedding a.val := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [MulEquiv.apply_symm_apply, map_mul, adelicRealGL2Embedding_coordinates,
      rationalAdelicFiniteGL2Embedding_coordinates]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rw [he]
  exact hv a _

/-- Proved strong approximation and the genuine invariance equations recover the entire positive component from its original classical real restriction. -/
theorem adelicFunction_positive_reconstruction (N : ℕ) [NeZero N] (k : ℤ)
    (v : RationalAdelicGL2 → ℂ) (F : ℍ → ℂ)
    (hr : ∀ γ : GeneralLinearGroup (Fin 2) ℚ, ∀ g,
      v (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) = v g)
    (hc : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (hl : ∀ a : finiteAdeleGL2Gamma0 N, ∀ g,
      v (g * rationalAdelicFiniteGL2Embedding a.val) = v g)
    (hF : ∀ g : SL(2, ℝ), v (adelicRealSL2Embedding g) = realWeightLift k F g)
    (g : GL(2, ℝ)⁺) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    v (rationalAdelicGL2RealFiniteEquiv.symm (g.val, a)) = positiveAdelicGL2CuspLift N k F g a := by
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N a
  let γ := positiveAdelicGL2Representative N a
  let b := (rationalPositiveGL2ToReal γ)⁻¹ * g
  have he := adelicFunction_rational_coordinates v hr γ.val b.val u.val
  have hm : rationalGL2ToReal γ.val * b.val = g.val := mul_inv_cancel_left _ _
  rw [hm] at he
  change v (rationalAdelicGL2RealFiniteEquiv.symm (g.val, rationalPositiveGL2ToFinite γ * u.val)) = _ at he
  rw [← hu] at he
  rw [he, adelicFunction_level_coordinates N v hl, adelicFunction_real_normalize v hc, hF]
  rfl

/-- Both actual real components and every finite coordinate are determined by the original classical restriction and the genuine invariance equations. -/
theorem adelicFunction_full_reconstruction (N : ℕ) [NeZero N] (k : ℤ)
    (v : RationalAdelicGL2 → ℂ) (F : ℍ → ℂ)
    (hr : ∀ γ : GeneralLinearGroup (Fin 2) ℚ, ∀ g,
      v (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) = v g)
    (hc : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (hl : ∀ a : finiteAdeleGL2Gamma0 N, ∀ g,
      v (g * rationalAdelicFiniteGL2Embedding a.val) = v g)
    (hF : ∀ g : SL(2, ℝ), v (adelicRealSL2Embedding g) = realWeightLift k F g) :
    v = canonicalAdelicGL2CuspLift N k F := by
  funext a
  obtain ⟨⟨g, x⟩, rfl⟩ := rationalAdelicGL2RealFiniteEquiv.symm.surjective a
  have he := adelicFunction_rational_coordinates v hr (realGL2RationalSign g)
    (realGL2PositivePart g).val ((rationalGL2ToFinite (realGL2RationalSign g))⁻¹ * x)
  have hm : rationalGL2ToReal (realGL2RationalSign g) * (realGL2PositivePart g).val = g :=
    mul_inv_cancel_left _ _
  rw [hm, mul_inv_cancel_left] at he
  rw [he, adelicFunction_positive_reconstruction N k v F hr hc hl hF]
  rw [canonicalAdelicGL2CuspLift_coordinates]
  rfl

end
end Dubon2026
