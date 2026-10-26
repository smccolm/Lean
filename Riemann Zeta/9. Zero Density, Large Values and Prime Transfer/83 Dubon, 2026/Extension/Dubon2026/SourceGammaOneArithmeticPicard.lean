import Dubon2026.SourceGammaOneArithmeticDivisors

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> actual arithmetic action on degree-zero divisor classes.
The same coefficient action preserves the proved geometric relations.
Reuse native quotient functoriality and the original place-action laws.
Hecke naturality is a separate consumer; no Galois association is claimed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {L : Type*} [Field L] [Algebra ℚ L]
local notation "FN" => functionFieldOver Γ L

theorem arithmeticPlace_one (v : Place L FN) :
    arithmeticPlace Γ (1 : L ≃ₐ[ℚ] L) v = v := by
  apply Place.ext
  ext x
  change arithmeticRingAut Γ (1 : L ≃ₐ[ℚ] L).symm x ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
  have he : arithmeticRingAut Γ (1 : L ≃ₐ[ℚ] L).symm x = x := by
    apply Subtype.ext
    ext n
    rfl
  rw [he]

theorem arithmeticPlace_mul (σ τ : L ≃ₐ[ℚ] L) (v : Place L FN) :
    arithmeticPlace Γ (σ * τ) v = arithmeticPlace Γ σ (arithmeticPlace Γ τ v) := by
  apply Place.ext
  ext x
  change arithmeticRingAut Γ (σ * τ).symm x ∈ v.toValuationSubring ↔
    arithmeticRingAut Γ τ.symm (arithmeticRingAut Γ σ.symm x) ∈ v.toValuationSubring
  have he : arithmeticRingAut Γ (σ * τ).symm x =
      arithmeticRingAut Γ τ.symm (arithmeticRingAut Γ σ.symm x) := by
    apply Subtype.ext
    ext n
    rfl
  rw [he]

theorem arithmeticDivisor_one (D : Divisor L FN) :
    arithmeticDivisorEquiv Γ (1 : L ≃ₐ[ℚ] L) D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
    rw [map_add, ih]
    change Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ 1) (Finsupp.single v n) + D = _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (arithmeticPlace Γ 1 v) n + D = _
    rw [arithmeticPlace_one]

theorem arithmeticDivisor_mul (σ τ : L ≃ₐ[ℚ] L) (D : Divisor L FN) :
    arithmeticDivisorEquiv Γ (σ * τ) D =
      arithmeticDivisorEquiv Γ σ (arithmeticDivisorEquiv Γ τ D) := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ (σ * τ)) (Finsupp.single v n) + _ =
      Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ σ)
        (Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ τ) (Finsupp.single v n)) + _
    simp only [Finsupp.equivMapDomain_single]
    change Finsupp.single (arithmeticPlace Γ (σ * τ) v) n + _ =
      Finsupp.single (arithmeticPlace Γ σ (arithmeticPlace Γ τ v)) n + _
    rw [arithmeticPlace_mul]

variable [Γ.FiniteIndex] [IsAlgClosed L] (hT : ModularGroup.T ∈ Γ)

/-- The genuine arithmetic action restricted to original degree-zero divisors. -/
def arithmeticDegZero (σ : L ≃ₐ[ℚ] L) :
    Divisor.degZero (K := L) (F := FN) →+ Divisor.degZero (K := L) (F := FN) where
  toFun D := ⟨arithmeticDivisorEquiv Γ σ D.val, by
    change Divisor.degree (arithmeticDivisorEquiv Γ σ D.val) = 0
    rw [arithmeticDivisor_degree Γ hT]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D E := Subtype.ext (map_add _ D.val E.val)

/-- Arithmetic transport descends through the actual principal-divisor relation. -/
def arithmeticPicard (σ : L ≃ₐ[ℚ] L) : Pic0 L FN →+ Pic0 L FN :=
  QuotientAddGroup.map _ _ (arithmeticDegZero Γ hT σ) (by
    intro D hD
    exact arithmeticDivisor_principal Γ σ D.val hD)

theorem arithmeticPicard_mk (σ : L ≃ₐ[ℚ] L)
    (D : Divisor.degZero (K := L) (F := FN)) :
    arithmeticPicard Γ hT σ (Pic0.mk D) = Pic0.mk (arithmeticDegZero Γ hT σ D) := rfl

/-- The original Galois coefficient action on the genuine degree-zero divisor classes. -/
def arithmeticPicardRep : (L ≃ₐ[ℚ] L) →* AddMonoid.End (Pic0 L FN) where
  toFun := arithmeticPicard Γ hT
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [arithmeticPicard_mk]
    exact congrArg Pic0.mk (Subtype.ext (arithmeticDivisor_one Γ D.val))
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    change arithmeticPicard Γ hT (σ * τ) (Pic0.mk D) =
      arithmeticPicard Γ hT σ (arithmeticPicard Γ hT τ (Pic0.mk D))
    rw [arithmeticPicard_mk, arithmeticPicard_mk, arithmeticPicard_mk]
    exact congrArg Pic0.mk (Subtype.ext (arithmeticDivisor_mul Γ σ τ D.val))

theorem arithmeticPicard_torsion (σ : L ≃ₐ[ℚ] L) (n : ℕ)
    (x : Pic0 L FN) (hx : x ∈ Pic0.torsion n) :
    arithmeticPicard Γ hT σ x ∈ Pic0.torsion n := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceFunctionField.GammaOne
