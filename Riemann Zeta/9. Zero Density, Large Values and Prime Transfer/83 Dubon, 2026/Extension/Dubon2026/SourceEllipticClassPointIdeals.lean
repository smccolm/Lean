import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic

/-! The affine ideal-class route to the actual odd cyclic quotient map.
Adapted from TauCetiProject/TauCeti, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba; the point-class argument
credits Chris Birkbeck's AINTLIB. Only the elliptic-curve consumer is
needed: omit singular-curve cotangent spaces and the general isogeny category.
Dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation ->
arithmetic automorphy -> Frobenius/inertia -> modular-curve good reduction ->
reverse genus and inertia census -> cyclic modular-polynomial roots ->
explicit odd quotient homomorphism -> norm-induced map of ideal classes. -/
namespace Dubon2026.SourceEllipticClassGroup
noncomputable section
open Polynomial WeierstrassCurve.Affine FractionalIdeal
open scoped nonZeroDivisors Polynomial.Bivariate TensorProduct
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
theorem algHom_mk_eq_evalEval (f : W.CoordinateRing →ₐ[F] F) (p : F[X][Y]) :
    f (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F F))).evalEval
        (f (AdjoinRoot.of W.polynomial X))
        (f (AdjoinRoot.root W.polynomial)) := by
  rw [← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X]
  let g : F[X][Y] →ₐ[F] F :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars F)
  -- Unfold the local abbreviation `g` so the polynomial evaluation equivalence sees its argument.
  change g p = _
  have hg : g = aevalAeval (g (C X)) (g Y) :=
    ((aevalAevalEquiv F F).apply_symm_apply g).symm
  rw [hg]
  let _ := Polynomial.algebra F F
  rw [aevalAevalEquiv_apply_apply, Polynomial.aeval_def, eval₂_eq_eval_map]
  have halg : algebraMap F[X] F[X] = mapRingHom (algebraMap F F) := rfl
  rw [halg]
  simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]


theorem equation_of_algHom (f : W.CoordinateRing →ₐ[F] F) :
    W.Equation (f (AdjoinRoot.of W.polynomial X))
      (f (AdjoinRoot.root W.polynomial)) := by
  have h := algHom_mk_eq_evalEval f W.polynomial
  rw [AdjoinRoot.mk_self, map_zero] at h
  simpa only [Equation, Algebra.algebraMap_self, Polynomial.mapRingHom_id,
    Polynomial.map_id] using h.symm

theorem mk_mem_XYIdeal_iff
    {x : F} {y : F[X]} (h : (W.polynomial.eval y).eval x = 0) (p : F[X][Y]) :
    CoordinateRing.mk W p ∈ CoordinateRing.XYIdeal W x y ↔ (p.eval y).eval x = 0 := by
  -- The curve relation lies in the polynomial point ideal, so quotienting preserves membership.
  have hle : Ideal.span {W.polynomial} ≤ Ideal.span {C (X - C x), Y - C y} :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h)
  rw [CoordinateRing.XYIdeal, CoordinateRing.XClass, CoordinateRing.YClass,
    ← Set.image_pair, ← Ideal.map_span]
  exact (Ideal.mem_quotient_iff_mem hle).trans
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero


theorem finrank_quotient_eq_one_iff {I : Ideal W.CoordinateRing} :
    Module.finrank F (W.CoordinateRing ⧸ I) = 1 ↔
      ∃ x y : F, W.Equation x y ∧ I = CoordinateRing.XYIdeal W x (C y) := by
  constructor
  · intro hdeg
    have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ I)) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg
    let e : (W.CoordinateRing ⧸ I) ≃ₐ[F] F :=
      (AlgEquiv.ofBijective (Algebra.ofId F _) hbij).symm
    let ρ : W.CoordinateRing →ₐ[F] F := e.toAlgHom.comp (Ideal.Quotient.mkₐ F I)
    have hρmem : ∀ a, ρ a = 0 ↔ a ∈ I := fun a ↦ by
      change e (Ideal.Quotient.mk I a) = 0 ↔ a ∈ I
      rw [map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
    have heq := equation_of_algHom ρ
    refine ⟨_, _, heq, ?_⟩
    ext a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [← hρmem, algHom_mk_eq_evalEval, mk_mem_XYIdeal_iff heq]
    simp only [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]
  · rintro ⟨x, y, h, rfl⟩
    rw [(CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

end
end Dubon2026.SourceEllipticClassGroup
