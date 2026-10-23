import Dubon2026.SourceEllipticClassPointIdeals
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! Actual elliptic coordinate-ring normality for the odd quotient map.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The direct local-principal-ideal
argument meets the algebraically closed source contract in all characteristics.
Reuse the actual point-ideal classification; defer arbitrary-field normality.
This discharges the coordinate-ring input to the norm-induced odd quotient map,
needed by cyclic modular-polynomial roots, inertia census, reverse genus and
good reduction on the DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain. -/
namespace Dubon2026.SourceEllipticClassGroup
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing IsLocalRing
open scoped Polynomial.Bivariate
noncomputable section
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
theorem XYIdeal_ne_bot (x : F) (y : F[X]) : XYIdeal W x y ≠ ⊥ := fun h0 =>
  XClass_ne_zero (W' := W) x <| by
    have : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (by simp)
    rwa [h0, Ideal.mem_bot] at this

theorem span_pair_eq_span_singleton_of_mul_eq {R : Type*} [CommRing R] {a b c u : R}
    (hu : IsUnit u) (h : b * u = a * c) : Ideal.span {a, b} = Ideal.span {a} := by
  refine le_antisymm (Ideal.span_le.mpr <| Set.insert_subset_iff.mpr
    ⟨Ideal.mem_span_singleton_self a, Set.singleton_subset_iff.mpr ?_⟩)
    (Ideal.span_mono <| Set.singleton_subset_iff.mpr <| Set.mem_insert _ _)
  obtain ⟨u, rfl⟩ := hu
  exact Ideal.mem_span_singleton'.mpr ⟨c * ↑u⁻¹, by
    rw [show c * ↑u⁻¹ * a = a * c * ↑u⁻¹ by ring, ← h, Units.mul_inv_cancel_right]⟩

theorem map_XYIdeal {S : Type*} [CommRing S] (f : W.CoordinateRing →+* S) (x : F) (y : F[X]) :
    (XYIdeal W x y).map f = Ideal.span {f (XClass W x), f (YClass W y)} := by
  rw [XYIdeal, Ideal.map_span, Set.image_pair]

theorem isPrincipal_maximalIdeal_localization {x y : F} (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    (maximalIdeal (Localization.AtPrime (XYIdeal W x (C y)))).IsPrincipal := by
  set L := Localization.AtPrime (XYIdeal W x (C y))
  have hI : maximalIdeal L =
      Ideal.span {algebraMap _ L (XClass W x), algebraMap _ L (YClass W (C y))} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, map_XYIdeal]

  set g : F[X][Y] := C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y
    with hg
  have key : YClass W (C y) * YClass W (C (W.negY x y)) = XClass W x * mk W g := by
    simp only [YClass, XClass, ← map_mul]
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by
      linear_combination (norm := (rw [hg, negY, polynomial]; simp only [C_neg, C_add, C_sub, C_mul, C_pow]; ring1))
        congr_arg C (congr_arg C ((equation_iff ..).mp h.left).symm)⟩
  have key' : algebraMap _ L (YClass W (C y)) * algebraMap _ L (YClass W (C (W.negY x y))) =
      algebraMap _ L (XClass W x) * algebraMap _ L (mk W g) := by
    rw [← map_mul, ← map_mul, key]
  have hmem : ∀ p : F[X][Y], mk W p ∈ XYIdeal W x (C y) ↔ p.evalEval x y = 0 :=
    mk_mem_XYIdeal_iff h.left
  rcases h.right with hx | hy
  ·
    have hgu : IsUnit (algebraMap _ L (mk W g)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L (XYIdeal W x (C y))]
      intro (hgI : mk W g ∈ XYIdeal W x (C y))
      apply hx
      have h0 := (hmem g).mp hgI
      rw [evalEval_polynomialX]
      simp only [hg, evalEval_sub, evalEval_mul, evalEval_C, evalEval_X, eval_add, eval_mul,
        eval_pow, eval_C, eval_X] at h0
      linear_combination -h0
    refine ⟨⟨algebraMap _ L (YClass W (C y)), ?_⟩⟩
    rw [hI, Ideal.span_insert, sup_comm, ← Ideal.span_insert]
    exact span_pair_eq_span_singleton_of_mul_eq hgu key'.symm
  ·
    have hyu : IsUnit (algebraMap _ L (YClass W (C (W.negY x y)))) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L (XYIdeal W x (C y))]
      intro (hyI : mk W (Y - C (C (W.negY x y))) ∈ XYIdeal W x (C y))
      apply hy
      have h0 := (hmem _).mp hyI
      rw [evalEval_polynomialY]
      simp only [evalEval_sub, evalEval_CC, evalEval_X, negY] at h0
      linear_combination h0
    refine ⟨⟨algebraMap _ L (XClass W x), ?_⟩⟩
    rw [hI]
    exact span_pair_eq_span_singleton_of_mul_eq hyu key'


end
end Dubon2026.SourceEllipticClassGroup
