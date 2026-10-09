import Dubon2026.AdelicInvariantReconstruction

/-! # Faithfulness of the original family of real restrictions at finite level translates -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- Trivial genuine scalar action normalizes the real coordinate even with an arbitrary fixed finite coordinate. -/
theorem adelicFunction_real_finite_normalize (v : RationalAdelicGL2 → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (g : GL(2, ℝ)⁺) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    v (adelicRealGL2Embedding g.val * rationalAdelicFiniteGL2Embedding a) =
      v (adelicRealSL2Embedding (realPositiveNormalize g) * rationalAdelicFiniteGL2Embedding a) := by
  apply adelicFunction_real_normalize (fun x => v (x * rationalAdelicFiniteGL2Embedding a))
  intro u x
  change v ((GeneralLinearGroup.scalar (Fin 2) u * x) * rationalAdelicFiniteGL2Embedding a) = _
  rw [mul_assoc]
  exact hv u _

/-- Proved rational strong approximation makes the entire finite-level family of genuine real restrictions faithful. -/
theorem adelicFunction_level_family_eq_zero (N : ℕ) [NeZero N]
    (v : RationalAdelicGL2 → ℂ)
    (hr : ∀ γ : GeneralLinearGroup (Fin 2) ℚ, ∀ g,
      v (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) = v g)
    (hc : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (hz : ∀ a : finiteAdeleGL2Gamma0 N, ∀ g : SL(2, ℝ),
      v (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding a.val) = 0) : v = 0 := by
  have hp (g : GL(2, ℝ)⁺) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
      v (rationalAdelicGL2RealFiniteEquiv.symm (g.val, a)) = 0 := by
    obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N a
    let γ := positiveAdelicGL2Representative N a
    let b := (rationalPositiveGL2ToReal γ)⁻¹ * g
    have he := adelicFunction_rational_coordinates v hr γ.val b.val u.val
    have hm : rationalGL2ToReal γ.val * b.val = g.val := mul_inv_cancel_left _ _
    rw [hm] at he
    change v (rationalAdelicGL2RealFiniteEquiv.symm (g.val, rationalPositiveGL2ToFinite γ * u.val)) = _ at he
    rw [← hu] at he
    rw [he]
    have hcoord : rationalAdelicGL2RealFiniteEquiv.symm (b.val, u.val) =
        adelicRealGL2Embedding b.val * rationalAdelicFiniteGL2Embedding u.val := by
      apply rationalAdelicGL2RealFiniteEquiv.injective
      rw [MulEquiv.apply_symm_apply, map_mul, adelicRealGL2Embedding_coordinates,
        rationalAdelicFiniteGL2Embedding_coordinates]
      simp only [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hcoord, adelicFunction_real_finite_normalize v hc]
    exact hz u _
  funext a
  obtain ⟨⟨g, x⟩, rfl⟩ := rationalAdelicGL2RealFiniteEquiv.symm.surjective a
  have he := adelicFunction_rational_coordinates v hr (realGL2RationalSign g)
    (realGL2PositivePart g).val ((rationalGL2ToFinite (realGL2RationalSign g))⁻¹ * x)
  have hm : rationalGL2ToReal (realGL2RationalSign g) * (realGL2PositivePart g).val = g :=
    mul_inv_cancel_left _ _
  rw [hm, mul_inv_cancel_left] at he
  rw [he]
  exact hp _ _

end
end Dubon2026
