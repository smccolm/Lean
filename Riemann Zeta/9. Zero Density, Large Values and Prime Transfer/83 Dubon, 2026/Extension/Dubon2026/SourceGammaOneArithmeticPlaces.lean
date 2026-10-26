import Dubon2026.SourceGammaOneArithmeticField
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> Galois/Hecke action on actual Picard classes.
Reuse the original arithmetic place construction on these actual modular
integral-ratio fields. Existing uniqueness of discrete order supplies the
exact order equation; no abstract semilinear-place framework is needed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {L : Type*} [Field L] [Algebra ℚ L]
local notation "F" => functionFieldOver Γ L

/-- The original valuation ring transported by the inverse coefficient action. -/
def arithmeticValuationEquiv (σ : L ≃ₐ[ℚ] L) (v : Place L F) :
    v.toValuationSubring.comap (arithmeticRingAut Γ σ.symm).toRingHom ≃+*
      v.toValuationSubring where
  toFun x := ⟨arithmeticRingAut Γ σ.symm x.val, x.property⟩
  invFun y := ⟨(arithmeticRingAut Γ σ.symm).symm y.val, by
    change arithmeticRingAut Γ σ.symm ((arithmeticRingAut Γ σ.symm).symm y.val) ∈ v.toValuationSubring
    rw [RingEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((arithmeticRingAut Γ σ.symm).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((arithmeticRingAut Γ σ.symm).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul (arithmeticRingAut Γ σ.symm) x.val y.val)
  map_add' x y := Subtype.ext (map_add (arithmeticRingAut Γ σ.symm) x.val y.val)

/-- Arithmetic transport of a place of the original modular function field. -/
def arithmeticPlace (σ : L ≃ₐ[ℚ] L) (v : Place L F) : Place L F where
  toValuationSubring := v.toValuationSubring.comap (arithmeticRingAut Γ σ.symm).toRingHom
  algebraMap_mem' a := by
    change arithmeticRingAut Γ σ.symm (algebraMap L F a) ∈ v.toValuationSubring
    rw [arithmeticRingAut_constants]
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
      have hy : (arithmeticRingAut Γ σ.symm).symm y ∈
          v.toValuationSubring.comap (arithmeticRingAut Γ σ.symm).toRingHom :=
        h ▸ ValuationSubring.mem_top _
      change arithmeticRingAut Γ σ.symm ((arithmeticRingAut Γ σ.symm).symm y) ∈ v.toValuationSubring at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
  isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective
    (arithmeticValuationEquiv Γ σ v).symm (arithmeticValuationEquiv Γ σ v).symm.surjective

theorem arithmeticPlace_ord (σ : L ≃ₐ[ℚ] L) (v : Place L F) (f : F) :
    (arithmeticPlace Γ σ v).ord f = v.ord (arithmeticRingAut Γ σ.symm f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  symm
  apply (arithmeticPlace Γ σ v).eq_ord_of_addHom_of_nonneg_iff
    (fun x => v.ord (arithmeticRingAut Γ σ.symm x))
  · intro x y hx hy
    rw [map_mul, v.ord_mul (by simpa using hx) (by simpa using hy)]
  · refine ⟨(arithmeticRingAut Γ σ.symm).symm v.uniformizer, ?_, ?_⟩
    · simpa only [map_zero] using
        (arithmeticRingAut Γ σ.symm).symm.injective.ne v.uniformizer_ne_zero
    · rw [RingEquiv.apply_symm_apply, v.ord_uniformizer]
  · intro x _
    exact v.mem_iff_ord_nonneg.symm
  · exact hf

/-- Arithmetic coefficient automorphisms permute all original places. -/
def arithmeticPlaceEquiv (σ : L ≃ₐ[ℚ] L) : Place L F ≃ Place L F where
  toFun := arithmeticPlace Γ σ
  invFun := arithmeticPlace Γ σ.symm
  left_inv v := by
    apply Place.ext
    ext x
    change arithmeticRingAut Γ σ.symm (arithmeticRingAut Γ σ.symm.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : arithmeticRingAut Γ σ.symm (arithmeticRingAut Γ σ.symm.symm x) = x := by
      apply Subtype.ext
      ext n
      exact σ.symm.apply_symm_apply (x.val.coeff n)
    rw [he]
  right_inv v := by
    apply Place.ext
    ext x
    change arithmeticRingAut Γ σ.symm.symm (arithmeticRingAut Γ σ.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : arithmeticRingAut Γ σ.symm.symm (arithmeticRingAut Γ σ.symm x) = x := by
      apply Subtype.ext
      ext n
      exact σ.symm.symm_apply_apply (x.val.coeff n)
    rw [he]

theorem arithmeticPlace_ord_action (σ : L ≃ₐ[ℚ] L) (v : Place L F) (f : F) :
    (arithmeticPlace Γ σ v).ord (arithmeticRingAut Γ σ f) = v.ord f := by
  rw [arithmeticPlace_ord]
  congr 1
  apply Subtype.ext
  ext n
  exact σ.symm_apply_apply (f.val.coeff n)

end
end Dubon2026.SourceFunctionField.GammaOne
