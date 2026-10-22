import Dubon2026.SourceOriginalArithmeticFieldAction
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> actual modular Galois association -> the original
divisor-class action. Coefficient automorphisms transport the literal
valuation rings of the same modular field. Existing uniqueness of the
normalized discrete order proves the exact arithmetic order equation.
This reuses the local place-transport argument; an abstract semilinear
automorphism framework is unnecessary for the required original action.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) {L : Type*} [Field L] [Algebra ℚ L]
local notation "F" => modularFunctionFieldOver N L

/-- The original valuation ring transported by the inverse coefficient action. -/
def originalArithmeticValuationEquiv (σ : L ≃ₐ[ℚ] L) (v : Place L F) :
    v.toValuationSubring.comap (originalArithmeticRingAut N σ.symm).toRingHom ≃+*
      v.toValuationSubring where
  toFun x := ⟨originalArithmeticRingAut N σ.symm x.val, x.property⟩
  invFun y := ⟨(originalArithmeticRingAut N σ.symm).symm y.val, by
    change originalArithmeticRingAut N σ.symm ((originalArithmeticRingAut N σ.symm).symm y.val) ∈ v.toValuationSubring
    rw [RingEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((originalArithmeticRingAut N σ.symm).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((originalArithmeticRingAut N σ.symm).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul (originalArithmeticRingAut N σ.symm) x.val y.val)
  map_add' x y := Subtype.ext (map_add (originalArithmeticRingAut N σ.symm) x.val y.val)

/-- Arithmetic transport of a place of the original modular function field. -/
def originalArithmeticPlace (σ : L ≃ₐ[ℚ] L) (v : Place L F) : Place L F where
  toValuationSubring := v.toValuationSubring.comap (originalArithmeticRingAut N σ.symm).toRingHom
  algebraMap_mem' a := by
    change originalArithmeticRingAut N σ.symm (algebraMap L F a) ∈ v.toValuationSubring
    rw [originalArithmeticRingAut_constants]
    exact v.algebraMap_mem' _
  ne_top' := by
    intro h
    apply v.ne_top'
    apply SetLike.ext
    intro y
    constructor
    · intro _
      exact ValuationSubring.mem_top y
    · intro _
      have hy : (originalArithmeticRingAut N σ.symm).symm y ∈
          v.toValuationSubring.comap (originalArithmeticRingAut N σ.symm).toRingHom :=
        h ▸ ValuationSubring.mem_top _
      change originalArithmeticRingAut N σ.symm ((originalArithmeticRingAut N σ.symm).symm y) ∈ v.toValuationSubring at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
  isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective
    (originalArithmeticValuationEquiv N σ v).symm (originalArithmeticValuationEquiv N σ v).symm.surjective

theorem originalArithmeticPlace_ord (σ : L ≃ₐ[ℚ] L) (v : Place L F) (f : F) :
    (originalArithmeticPlace N σ v).ord f = v.ord (originalArithmeticRingAut N σ.symm f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  symm
  apply (originalArithmeticPlace N σ v).eq_ord_of_addHom_of_nonneg_iff
    (fun x => v.ord (originalArithmeticRingAut N σ.symm x))
  · intro x y hx hy
    rw [map_mul, v.ord_mul (by simpa using hx) (by simpa using hy)]
  · refine ⟨(originalArithmeticRingAut N σ.symm).symm v.uniformizer, ?_, ?_⟩
    · simpa only [map_zero] using
        (originalArithmeticRingAut N σ.symm).symm.injective.ne v.uniformizer_ne_zero
    · rw [RingEquiv.apply_symm_apply, v.ord_uniformizer]
  · intro x _
    exact v.mem_iff_ord_nonneg.symm
  · exact hf

/-- Arithmetic coefficient automorphisms permute all original places. -/
def originalArithmeticPlaceEquiv (σ : L ≃ₐ[ℚ] L) : Place L F ≃ Place L F where
  toFun := originalArithmeticPlace N σ
  invFun := originalArithmeticPlace N σ.symm
  left_inv v := by
    apply Place.ext
    ext x
    change originalArithmeticRingAut N σ.symm (originalArithmeticRingAut N σ.symm.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : originalArithmeticRingAut N σ.symm (originalArithmeticRingAut N σ.symm.symm x) = x := by
      apply Subtype.ext
      ext n
      exact σ.symm.apply_symm_apply (x.val.coeff n)
    rw [he]
  right_inv v := by
    apply Place.ext
    ext x
    change originalArithmeticRingAut N σ.symm.symm (originalArithmeticRingAut N σ.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : originalArithmeticRingAut N σ.symm.symm (originalArithmeticRingAut N σ.symm x) = x := by
      apply Subtype.ext
      ext n
      exact σ.symm.symm_apply_apply (x.val.coeff n)
    rw [he]

theorem originalArithmeticPlace_ord_action (σ : L ≃ₐ[ℚ] L) (v : Place L F) (f : F) :
    (originalArithmeticPlace N σ v).ord (originalArithmeticRingAut N σ f) = v.ord f := by
  rw [originalArithmeticPlace_ord]
  congr 1
  apply Subtype.ext
  ext n
  exact σ.symm_apply_apply (f.val.coeff n)

end
end Dubon2026.SourceFunctionField
