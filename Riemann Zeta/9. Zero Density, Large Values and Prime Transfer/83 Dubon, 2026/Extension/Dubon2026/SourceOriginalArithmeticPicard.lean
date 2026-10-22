import Dubon2026.SourceOriginalArithmeticDivisors

/-! DUB-17/18 -> original modular Galois association -> the Tate module
of the actual original divisor-class group. The literal coefficient
action preserves the original degree-zero and principal relations, so
native quotient functoriality gives its arithmetic action on Pic0.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) {L : Type*} [Field L] [Algebra ℚ L]
local notation "FN" => modularFunctionFieldOver N L

theorem originalArithmeticPlace_one (v : Place L FN) :
    originalArithmeticPlace N (1 : L ≃ₐ[ℚ] L) v = v := by
  apply Place.ext
  ext x
  change originalArithmeticRingAut N (1 : L ≃ₐ[ℚ] L).symm x ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
  have he : originalArithmeticRingAut N (1 : L ≃ₐ[ℚ] L).symm x = x := by
    apply Subtype.ext
    ext n
    rfl
  rw [he]

theorem originalArithmeticPlace_mul (σ τ : L ≃ₐ[ℚ] L) (v : Place L FN) :
    originalArithmeticPlace N (σ * τ) v = originalArithmeticPlace N σ (originalArithmeticPlace N τ v) := by
  apply Place.ext
  ext x
  change originalArithmeticRingAut N (σ * τ).symm x ∈ v.toValuationSubring ↔
    originalArithmeticRingAut N τ.symm (originalArithmeticRingAut N σ.symm x) ∈ v.toValuationSubring
  have he : originalArithmeticRingAut N (σ * τ).symm x =
      originalArithmeticRingAut N τ.symm (originalArithmeticRingAut N σ.symm x) := by
    apply Subtype.ext
    ext n
    rfl
  rw [he]

theorem originalArithmeticDivisor_one (D : Divisor L FN) :
    originalArithmeticDivisorEquiv N (1 : L ≃ₐ[ℚ] L) D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
    rw [map_add, ih]
    change Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N 1) (Finsupp.single v n) + D = _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (originalArithmeticPlace N 1 v) n + D = _
    rw [originalArithmeticPlace_one]

theorem originalArithmeticDivisor_mul (σ τ : L ≃ₐ[ℚ] L) (D : Divisor L FN) :
    originalArithmeticDivisorEquiv N (σ * τ) D =
      originalArithmeticDivisorEquiv N σ (originalArithmeticDivisorEquiv N τ D) := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N (σ * τ)) (Finsupp.single v n) + _ =
      Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N σ)
        (Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N τ) (Finsupp.single v n)) + _
    simp only [Finsupp.equivMapDomain_single]
    change Finsupp.single (originalArithmeticPlace N (σ * τ) v) n + _ =
      Finsupp.single (originalArithmeticPlace N σ (originalArithmeticPlace N τ v)) n + _
    rw [originalArithmeticPlace_mul]

variable [NeZero N] [IsAlgClosed L]

/-- The genuine arithmetic action restricted to original degree-zero divisors. -/
def originalArithmeticDegZero (σ : L ≃ₐ[ℚ] L) :
    Divisor.degZero (K := L) (F := FN) →+ Divisor.degZero (K := L) (F := FN) where
  toFun D := ⟨originalArithmeticDivisorEquiv N σ D.val, by
    change Divisor.degree (originalArithmeticDivisorEquiv N σ D.val) = 0
    rw [originalArithmeticDivisor_degree]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D E := Subtype.ext (map_add _ D.val E.val)

/-- Arithmetic transport descends through the actual principal-divisor relation. -/
def originalArithmeticPicard (σ : L ≃ₐ[ℚ] L) : Pic0 L FN →+ Pic0 L FN :=
  QuotientAddGroup.map _ _ (originalArithmeticDegZero N σ) (by
    intro D hD
    exact originalArithmeticDivisor_principal N σ D.val hD)

theorem originalArithmeticPicard_mk (σ : L ≃ₐ[ℚ] L)
    (D : Divisor.degZero (K := L) (F := FN)) :
    originalArithmeticPicard N σ (Pic0.mk D) = Pic0.mk (originalArithmeticDegZero N σ D) := rfl

/-- The original Galois coefficient action on the genuine degree-zero divisor classes. -/
def originalArithmeticPicardRep : (L ≃ₐ[ℚ] L) →* AddMonoid.End (Pic0 L FN) where
  toFun := originalArithmeticPicard N
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [originalArithmeticPicard_mk]
    exact congrArg Pic0.mk (Subtype.ext (originalArithmeticDivisor_one N D.val))
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    change originalArithmeticPicard N (σ * τ) (Pic0.mk D) =
      originalArithmeticPicard N σ (originalArithmeticPicard N τ (Pic0.mk D))
    rw [originalArithmeticPicard_mk, originalArithmeticPicard_mk, originalArithmeticPicard_mk]
    exact congrArg Pic0.mk (Subtype.ext (originalArithmeticDivisor_mul N σ τ D.val))

theorem originalArithmeticPicard_torsion (σ : L ≃ₐ[ℚ] L) (n : ℕ)
    (x : Pic0 L FN) (hx : x ∈ Pic0.torsion n) :
    originalArithmeticPicard N σ x ∈ Pic0.torsion n := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceFunctionField
