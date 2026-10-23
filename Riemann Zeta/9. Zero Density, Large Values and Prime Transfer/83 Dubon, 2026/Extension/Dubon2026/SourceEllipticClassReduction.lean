import Dubon2026.SourceEllipticClassCodimension
import Dubon2026.SourceEllipticClassSmallNorm

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
theorem exists_codimLEOne_inv_integral
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
    ∃ (J : Ideal W.CoordinateRing)
      (hJunit : IsUnit (J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk W.FunctionField hJunit.unit =
          (ClassGroup.mk W.FunctionField hIunit.unit)⁻¹ := by
  have hIne : I ≠ ⊥ := by
    intro h
    apply hIunit.ne_zero
    simp [h]
  obtain ⟨a, ha_mem, ha, hbound⟩ := exists_mem_norm_natDegree_le (F := F) I hIne
  obtain ⟨J, hJunit, hJne, hJ⟩ :=
    exists_isUnit_span_singleton_eq_mul I hIunit ha ha_mem
  have haK : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField).ne ha
  refine ⟨J, hJunit, ?_, ?_⟩
  · -- Codimension is additive on the factorisation `⟨a⟩ = I * J`, and `⟨a⟩` has codimension
    -- the degree of the norm of `a`, which was chosen at most one more than that of `I`.
    have hdim : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        Module.finrank F (W.CoordinateRing ⧸ I) +
          Module.finrank F (W.CoordinateRing ⧸ J) := by
      rw [hJ]
      have : Module.Finite F (W.CoordinateRing ⧸ I) :=
        finiteDimensional_quotient_of_ne_bot _ hIne
      have : Module.Finite F (W.CoordinateRing ⧸ J) :=
        finiteDimensional_quotient_of_ne_bot _ hJne
      let : Module.Invertible W.CoordinateRing I :=
        moduleInvertible_of_isUnit_fractionalIdeal I hIunit
      have : Module.Finite F (W.CoordinateRing ⧸ I * J) :=
        finiteDimensional_quotient_of_ne_bot _ (by
          rw [← hJ]
          exact Ideal.span_singleton_eq_bot.not.mpr ha)
      exact finrank_quotient_mul F I J
    have hnorm : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        (Algebra.norm F[X] a).natDegree :=
      finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) ha
    omega
  · rw [eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk_eq_one_iff]
    refine ⟨Units.mk0 _ haK, ?_⟩
    rw [Units.val_mul, hJunit.unit_spec, hIunit.unit_spec,
      ← FractionalIdeal.coeIdeal_mul, mul_comm J I, ← hJ,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coe_spanSingleton]
    simp

/-- Every fractional ideal class has an inverse-class integral representative of codimension at
most one. -/
theorem exists_codimLEOne_inv
    (U : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
    ∃ (J : Ideal W.CoordinateRing)
      (hJunit : IsUnit (J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk W.FunctionField hJunit.unit =
          (ClassGroup.mk W.FunctionField U)⁻¹ := by
  let hIunit : IsUnit (U.1.num :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
    isUnit_num_iff.mpr U.isUnit
  obtain ⟨J, hJunit, hfin, hclass⟩ :=
    exists_codimLEOne_inv_integral (F := F) U.1.num hIunit
  refine ⟨J, hJunit, hfin, ?_⟩
  rwa [mk_num U] at hclass

theorem mk_eq_one_of_finrank_quotient_eq_zero
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField))
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 0) :
    ClassGroup.mk W.FunctionField hIunit.unit = 1 := by
  have : FiniteDimensional F (W.CoordinateRing ⧸ I) :=
    finiteDimensional_quotient_of_ne_bot _ (by
      intro h
      apply hIunit.ne_zero
      simp [h])
  have hsub : Subsingleton (W.CoordinateRing ⧸ I) := Module.finrank_zero_iff.mp hfin
  have htop : I = ⊤ := by
    rw [Ideal.Quotient.subsingleton_iff] at hsub
    exact hsub
  rw [ClassGroup.mk_eq_one_iff]
  refine ⟨1, ?_⟩
  rw [hIunit.unit_spec, htop, FractionalIdeal.coeIdeal_top, FractionalIdeal.coe_one,
    Submodule.one_eq_span]


end
end Dubon2026.SourceEllipticClassGroup
