import Dubon2026.SourceCurvePrincipalDivisorTransport
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original all-weight association -> actual arithmetic
Gamma1 diamond/Picard comparison. Reuse literal valuation-ring transport,
the exact order identity and principal-divisor transport. This construction
is needed for both the original arithmetic and complex diamond fields;
their already proved residue bijections discharge the visible degree input.
No period identification is used to define the Picard action.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
variable (e : F ≃ₐ[K] E)

/-- Transport actual divisors along the place permutation of the field equivalence. -/
def fieldDivisorEquiv : Divisor K F ≃+ Divisor K E :=
  Finsupp.domCongr (Place.placeEquiv e).symm

theorem fieldDivisorEquiv_apply (D : Divisor K F) (P : Place K F) :
    fieldDivisorEquiv e D ((Place.placeEquiv e).symm P) = D P := by
  change Finsupp.equivMapDomain (Place.placeEquiv e).symm D
    ((Place.placeEquiv e).symm P) = D P
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem fieldDivisorEquiv_principal_iff (D : Divisor K F) :
    Divisor.IsPrincipal (fieldDivisorEquiv e D) ↔ Divisor.IsPrincipal D := by
  constructor
  · rintro ⟨f, hf, hD⟩
    refine ⟨e.symm f, (map_ne_zero _).mpr hf, fun P => ?_⟩
    have hh := hD ((Place.placeEquiv e).symm P)
    rw [fieldDivisorEquiv_apply] at hh
    exact hh.trans (P.ord_comapEquiv e.symm f)
  · rintro ⟨f, hf, hD⟩
    exact ⟨e f, (map_ne_zero _).mpr hf, divisorTransform_orders e hD⟩

variable (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
variable (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))

include hF hE in
theorem fieldDivisorEquiv_degree (D : Divisor K F) :
    Divisor.degree (fieldDivisorEquiv e D) = Divisor.degree D :=
  degree_divisorTransform e D hF hE

/-- The same divisor transport restricted to the original degree-zero groups. -/
def fieldDegZeroEquiv :
    Divisor.degZero (K := K) (F := F) ≃+ Divisor.degZero (K := K) (F := E) where
  toFun D := ⟨fieldDivisorEquiv e D.val, by
    change Divisor.degree (fieldDivisorEquiv e D.val) = 0
    rw [fieldDivisorEquiv_degree e hF hE]
    exact D.property⟩
  invFun D := ⟨(fieldDivisorEquiv e).symm D.val, by
    change Divisor.degree ((fieldDivisorEquiv e).symm D.val) = 0
    rw [← fieldDivisorEquiv_degree e hF hE, AddEquiv.apply_symm_apply]
    exact D.property⟩
  left_inv D := Subtype.ext ((fieldDivisorEquiv e).symm_apply_apply D.val)
  right_inv D := Subtype.ext ((fieldDivisorEquiv e).apply_symm_apply D.val)
  map_add' D E := Subtype.ext (map_add (fieldDivisorEquiv e) D.val E.val)

theorem fieldDegZeroEquiv_principal :
    ((Divisor.principal (K := K) (F := F)).addSubgroupOf Divisor.degZero).map
        (fieldDegZeroEquiv e hF hE).toAddMonoidHom =
      (Divisor.principal (K := K) (F := E)).addSubgroupOf Divisor.degZero := by
  ext D
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (fieldDivisorEquiv_principal_iff e A.val).mpr hA
  · intro hD
    refine ⟨(fieldDegZeroEquiv e hF hE).symm D, ?_,
      (fieldDegZeroEquiv e hF hE).apply_symm_apply D⟩
    change Divisor.IsPrincipal ((fieldDegZeroEquiv e hF hE).symm D).val
    apply (fieldDivisorEquiv_principal_iff e _).mp
    change Divisor.IsPrincipal
      ((fieldDegZeroEquiv e hF hE) ((fieldDegZeroEquiv e hF hE).symm D)).val
    rw [AddEquiv.apply_symm_apply]
    exact hD

/-- The genuine degree-zero Picard equivalence induced by the field equivalence. -/
def fieldPicardEquiv : Pic0 K F ≃+ Pic0 K E :=
  QuotientAddGroup.congr _ _ (fieldDegZeroEquiv e hF hE)
    (fieldDegZeroEquiv_principal e hF hE)

theorem fieldPicardEquiv_mk (D : Divisor.degZero (K := K) (F := F)) :
    fieldPicardEquiv e hF hE (Pic0.mk D) = Pic0.mk (fieldDegZeroEquiv e hF hE D) := rfl

theorem fieldPicardEquiv_torsion (n : ℕ) (x : Pic0 K F) (hx : x ∈ Pic0.torsion n) :
    fieldPicardEquiv e hF hE x ∈ Pic0.torsion n := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceCurve
