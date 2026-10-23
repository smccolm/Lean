import Dubon2026.SourceEllipticClassReduction
import Dubon2026.SourceEllipticClassPointIdeals

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
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
open WeierstrassCurve.Affine.Point
theorem mk_eq_mk_XYIdeal'_of_finrank_quotient_eq_one
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField))
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (h : W.Nonsingular x y),
      ClassGroup.mk W.FunctionField hIunit.unit =
        ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  obtain ⟨x, y, heq, hxy⟩ :=
    finrank_quotient_eq_one_iff.mp hfin
  have hns : W.Nonsingular x y := W.equation_iff_nonsingular.mp heq
  refine ⟨x, y, hns, ?_⟩
  congr 1
  apply Units.ext
  rw [hIunit.unit_spec, CoordinateRing.XYIdeal'_eq hns, hxy]

/-! ## Surjectivity and the class-group equivalence -/

section DecidableEq

variable [DecidableEq F]

omit [W.IsElliptic] in
/-- The point-to-class map is surjective exactly when every ideal class is trivial or the
class of the point ideal at a nonsingular affine point. -/
theorem toClass_surjective_iff :
    Function.Surjective (toClass (W := W)) ↔ ∀ g : ClassGroup W.CoordinateRing,
      g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
        g = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) := by
  constructor
  · intro hsurj g
    obtain ⟨P, hP⟩ := hsurj (Additive.ofMul g)
    cases P with
    | zero =>
        left
        rw [← zero_def, toClass_zero] at hP
        exact (Additive.ofMul.injective hP).symm
    | some x y h =>
        right
        refine ⟨x, y, h, ?_⟩
        rw [toClass_some] at hP
        exact (Additive.ofMul.injective hP).symm
  · intro hrep c
    obtain hg | ⟨x, y, h, hg⟩ := hrep (Additive.toMul c)
    · -- `ofMul_one` names the step `Additive.ofMul 1 = 0`, so the trivial branch closes without
      -- appealing to the type synonym at all.
      exact ⟨0, by rw [toClass_zero, ← ofMul_toMul c, hg, ofMul_one]⟩
    · refine ⟨some x y h, ?_⟩
      rw [toClass_some, ← ofMul_toMul c, hg]
      -- What is left is `g = Additive.ofMul g`. `Additive.ofMul` is `Equiv.refl` on the
      -- underlying type and Mathlib names no lemma for it at a general element, so this last
      -- step is the type synonym and nothing else.
      rfl

/-- **The point-to-class map is surjective.** Equivalently, every ideal
class of its affine coordinate ring is represented by a rational point. -/
theorem toClass_surjective : Function.Surjective (toClass (W := W)) := by
  rw [toClass_surjective_iff]
  intro g
  refine ClassGroup.induction W.FunctionField (x := g) ?_
  intro U
  obtain ⟨J, hJunit, hfin, hclass⟩ := exists_codimLEOne_inv (F := F) U⁻¹
  rw [map_inv, inv_inv] at hclass
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfin with hzero | hone
  · left
    have htrivial := mk_eq_one_of_finrank_quotient_eq_zero J hJunit hzero
    exact hclass.symm.trans htrivial
  · right
    obtain ⟨x, y, hns, hpoint⟩ :=
      mk_eq_mk_XYIdeal'_of_finrank_quotient_eq_one J hJunit hone
    exact ⟨x, y, hns, hclass.symm.trans hpoint⟩

/-- **The points are their affine ideal class group.** -/
noncomputable def toClassEquiv :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective toClass ⟨toClass_injective, toClass_surjective⟩

/-- The point-to-class equivalence has underlying map `Point.toClass`. -/
@[simp]
theorem toClassEquiv_apply (P : W.Point) : toClassEquiv P = toClass P :=
  by
    unfold toClassEquiv
    exact AddEquiv.ofBijective_apply toClass _ P


end DecidableEq

end
end Dubon2026.SourceEllipticClassGroup
