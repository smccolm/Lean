import Dubon2026.AdelicReflectedWeightProjection

/-! # The actual lowest-weight projection of every original full adelic orbit vector -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem projection_product_scalar {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (P : V →ₗ[ℂ] V) (a b : G) (v : V) (c : ℂ)
    (hp : ∀ w, P (ρ a w) = ρ a (P w)) (hc : P (ρ b v) = c • v) :
    P (ρ (a * b) v) = c • ρ a v := by
  rw [map_mul, Module.End.mul_apply, hp, hc, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Both genuine real determinant components project to the original cusp generator line. -/
theorem adelicRotationWeightProjection_realGLOrbit (hf : f ≠ 0) (hk : 0 < k)
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    ∃ c : ℂ, adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f)) =
        c • adelicCyclicHilbertGenerator f := by
  by_cases hg : g ∈ GLPos (Fin 2) ℝ
  · have he := adelicCyclicHilbert_positive_normalize f (⟨g, hg⟩ : GL(2, ℝ)⁺)
      (adelicCyclicHilbertGenerator f)
    rw [he]
    exact adelicRotationWeightProjection_realOrbit f hf (realPositiveNormalize ⟨g, hg⟩)
  · change ¬0 < (GeneralLinearGroup.det g).val at hg
    have he : g = rationalGL2ToReal rationalGL2Reflection * (realGL2PositivePart g).val := by
      change g = rationalGL2ToReal rationalGL2Reflection *
        ((rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g)
      rw [realGL2RationalSign, if_neg hg]
      simp only [mul_inv_cancel_left]
    refine ⟨0, ?_⟩
    rw [he, map_mul, map_mul, Module.End.mul_apply,
      adelicCyclicHilbert_positive_normalize f (realGL2PositivePart g)]
    have hz := adelicRotationWeightProjection_reflectedReal f hf hk _
      (adelicRealCyclicClosedSpan_orbit_mem f (realPositiveNormalize (realGL2PositivePart g)))
    exact hz.trans (@zero_smul ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
      (adelicCyclicHilbertGenerator f)).symm

/-- Every original full adelic translate projects to a scalar multiple of its actual finite-coordinate translate. -/
theorem adelicRotationWeightProjection_fullOrbit (hf : f ≠ 0) (hk : 0 < k)
    (g : RationalAdelicGL2) :
    ∃ c : ℂ, adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) =
      c • adelicCyclicHilbertRepresentation f
        (rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv g).2)
        (adelicCyclicHilbertGenerator f) := by
  let a := (rationalAdelicGL2RealFiniteEquiv g).2
  let r := (rationalAdelicGL2RealFiniteEquiv g).1
  have he : g = rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding r := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates,
      adelicRealGL2Embedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]
    exact (Prod.eta _).symm
  obtain ⟨c, hc⟩ := adelicRotationWeightProjection_realGLOrbit f hf hk r
  refine ⟨c, ?_⟩
  change adelicRotationWeightProjection f
    (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) =
      c • adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertGenerator f)
  have hz := @projection_product_scalar RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicRotationWeightProjection f).toLinearMap (rationalAdelicFiniteGL2Embedding a)
    (adelicRealGL2Embedding r) (adelicCyclicHilbertGenerator f) c
    (adelicRotationWeightProjection_finite f a) hc
  exact (congrArg (fun h : RationalAdelicGL2 => adelicRotationWeightProjection f
    (adelicCyclicHilbertRepresentation f h (adelicCyclicHilbertGenerator f))) he).trans hz

end
end Dubon2026
