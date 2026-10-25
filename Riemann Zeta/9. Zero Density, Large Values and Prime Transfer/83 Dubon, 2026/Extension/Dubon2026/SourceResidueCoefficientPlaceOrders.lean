import Dubon2026.SourceResidueCoefficientPlaces

/-! DUB-17/18 -> original Frobenius/Picard comparison -> the actual
residue coefficient action on principal divisors. Reuse normalized discrete
order uniqueness and the inverse coefficient action to obtain the required
order-preserving permutation. These are the precise missing inputs to the
existing divisor and Picard quotient descent. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

theorem residueCoefficientPlace_ord (e : K ≃+* K) (v : Place K FF) (f : FF) :
    (residueCoefficientPlace N K e v).ord f = v.ord (residueCoefficientRingAut N K e.symm f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  symm
  apply (residueCoefficientPlace N K e v).eq_ord_of_addHom_of_nonneg_iff
    (fun x => v.ord (residueCoefficientRingAut N K e.symm x))
  · intro x y hx hy
    rw [map_mul, v.ord_mul (by simpa using hx) (by simpa using hy)]
  · refine ⟨(residueCoefficientRingAut N K e.symm).symm v.uniformizer, ?_, ?_⟩
    · simpa only [map_zero] using
        (residueCoefficientRingAut N K e.symm).symm.injective.ne v.uniformizer_ne_zero
    · rw [RingEquiv.apply_symm_apply, v.ord_uniformizer]
  · intro x _
    exact v.mem_iff_ord_nonneg.symm
  · exact hf

/-- Arithmetic coefficient automorphisms permute all residue places. -/
def residueCoefficientPlaceEquiv (e : K ≃+* K) : Place K FF ≃ Place K FF where
  toFun := residueCoefficientPlace N K e
  invFun := residueCoefficientPlace N K e.symm
  left_inv v := by
    apply Place.ext
    ext x
    change residueCoefficientRingAut N K e.symm (residueCoefficientRingAut N K e.symm.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : residueCoefficientRingAut N K e.symm (residueCoefficientRingAut N K e.symm.symm x) = x := by
      apply Subtype.ext
      ext n
      exact e.symm.apply_symm_apply (x.val.coeff n)
    rw [he]
  right_inv v := by
    apply Place.ext
    ext x
    change residueCoefficientRingAut N K e.symm.symm (residueCoefficientRingAut N K e.symm x) ∈
      v.toValuationSubring ↔ x ∈ v.toValuationSubring
    have he : residueCoefficientRingAut N K e.symm.symm (residueCoefficientRingAut N K e.symm x) = x := by
      apply Subtype.ext
      ext n
      exact e.symm.symm_apply_apply (x.val.coeff n)
    rw [he]

theorem residueCoefficientPlace_ord_action (e : K ≃+* K) (v : Place K FF) (f : FF) :
    (residueCoefficientPlace N K e v).ord (residueCoefficientRingAut N K e f) = v.ord f := by
  rw [residueCoefficientPlace_ord]
  congr 1
  apply Subtype.ext
  ext n
  exact e.symm_apply_apply (f.val.coeff n)

end
end Dubon2026.SourceFunctionField
