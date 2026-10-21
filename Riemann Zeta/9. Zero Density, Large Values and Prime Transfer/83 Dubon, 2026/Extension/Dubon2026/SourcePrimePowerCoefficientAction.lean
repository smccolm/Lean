import Dubon2026.SourcePrimeConjugateBaseChange
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.Finite.Basic

/-! DUB-17/18 -> numerical modular genus -> exact composite j-map degree
-> rational prime-power extension degree. The nonzero twisted roots form
one orbit under the actual cyclotomic coefficient automorphism. This is
the needed lower-degree argument after removing the previous-level root;
SourcePrimePowerExactFieldDegree assembles the degree consumer under
the explicit next-series nonmembership condition, which remains required.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean.
Existing literal twist coordinates and coefficient transport are reused.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
theorem qExpand_TS (m e : ℕ) [NeZero m] [NeZero e] (u : Kˣ) :
    qExpand K m (TS K e u) = TS K (m * e) u := by
  rw [TS, qExpand_qExpand]
  rfl

omit [Algebra ℚ K] in
theorem TS_congr {e e' : ℕ} [NeZero e] [NeZero e'] (h : e = e') (u : Kˣ) :
    TS K e u = TS K e' u := by
  subst h
  rfl

theorem coeffMap_TS {E : Type*} [Field E] [Algebra ℚ E]
    (σ : K →ₐ[ℚ] E) (e : ℕ) [NeZero e] (u : Kˣ) :
    coeffMap σ.toRingHom (TS K e u) =
      TS E e (Units.map σ.toRingHom.toMonoidHom u) := by
  rw [TS, TS, coeffMap_qExpand, coeffMap_qTwist_units,
    ← coeffEmb_jq K, ← coeffEmb_jq E, coeffMap_coeffEmb_algHom]

/-- The actual Laurent coefficient action of a rational coefficient-field automorphism. -/
def coeffMapEquiv (τ : K ≃ₐ[ℚ] K) : LaurentSeries K ≃+* LaurentSeries K where
  toFun := coeffMap ((τ : K →ₐ[ℚ] K) : K →+* K)
  invFun := coeffMap ((τ.symm : K →ₐ[ℚ] K) : K →+* K)
  left_inv := fun f => by
    show coeffMap ((τ.symm : K →ₐ[ℚ] K) : K →+* K)
        (coeffMap ((τ : K →ₐ[ℚ] K) : K →+* K) f) = f
    have hcomp : ((τ.symm : K →ₐ[ℚ] K) : K →+* K).comp ((τ : K →ₐ[ℚ] K) : K →+* K)
        = RingHom.id K := RingHom.ext fun x => τ.symm_apply_apply x
    rw [coeffMap_coeffMap, coeffMap_congr hcomp f, coeffMap_id]
  right_inv := fun f => by
    show coeffMap ((τ : K →ₐ[ℚ] K) : K →+* K)
        (coeffMap ((τ.symm : K →ₐ[ℚ] K) : K →+* K) f) = f
    have hcomp : ((τ : K →ₐ[ℚ] K) : K →+* K).comp ((τ.symm : K →ₐ[ℚ] K) : K →+* K)
        = RingHom.id K := RingHom.ext fun x => τ.apply_symm_apply x
    rw [coeffMap_coeffMap, coeffMap_congr hcomp f, coeffMap_id]
  map_mul' := map_mul _
  map_add' := map_add _

@[scoped simp] theorem coeffMapEquiv_apply (τ : K ≃ₐ[ℚ] K) (f : LaurentSeries K) :
    coeffMapEquiv τ f = coeffMap ((τ : K →ₐ[ℚ] K) : K →+* K) f := rfl


end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
