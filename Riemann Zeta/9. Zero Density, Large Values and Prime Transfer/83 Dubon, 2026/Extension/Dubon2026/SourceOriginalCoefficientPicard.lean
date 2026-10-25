import Dubon2026.SourceOriginalCoefficientDivisors

/-! DUB-17/18 -> original Picard inertia -> the same original divisor
classes in the coefficient-field reduction. The existing divisor
equivalence preserves degree and reflects principal divisors, so native
subgroup and quotient constructions give an actual Picard equivalence. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "FF" => modularFunctionFieldCoeff N Qbar

/-- Identification of degree-zero divisors on the two equal modular fields. -/
def originalCoefficientDegZeroEquiv :
    Divisor.degZero (K := Qbar) (F := Fo) ≃+ Divisor.degZero (K := Qbar) (F := FF) where
  toFun D := ⟨originalCoefficientDivisorEquiv N D.val, by
    change Divisor.degree (originalCoefficientDivisorEquiv N D.val) = 0
    rw [originalCoefficientDivisor_degree]
    exact D.property⟩
  invFun D := ⟨(originalCoefficientDivisorEquiv N).symm D.val, by
    change Divisor.degree ((originalCoefficientDivisorEquiv N).symm D.val) = 0
    rw [← originalCoefficientDivisor_degree N, AddEquiv.apply_symm_apply]
    exact D.property⟩
  left_inv D := Subtype.ext ((originalCoefficientDivisorEquiv N).symm_apply_apply D.val)
  right_inv D := Subtype.ext ((originalCoefficientDivisorEquiv N).apply_symm_apply D.val)
  map_add' D E := Subtype.ext (map_add (originalCoefficientDivisorEquiv N) D.val E.val)

theorem originalCoefficientDegZero_principal :
    ((Divisor.principal (K := Qbar) (F := Fo)).addSubgroupOf Divisor.degZero).map
        (originalCoefficientDegZeroEquiv N).toAddMonoidHom =
      (Divisor.principal (K := Qbar) (F := FF)).addSubgroupOf Divisor.degZero := by
  ext D
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact (originalCoefficientDivisor_principal_iff N E.val).mpr hE
  · intro hD
    refine ⟨(originalCoefficientDegZeroEquiv N).symm D, ?_,
      (originalCoefficientDegZeroEquiv N).apply_symm_apply D⟩
    change Divisor.IsPrincipal ((originalCoefficientDegZeroEquiv N).symm D).val
    apply (originalCoefficientDivisor_principal_iff N _).mp
    change Divisor.IsPrincipal
      ((originalCoefficientDegZeroEquiv N) ((originalCoefficientDegZeroEquiv N).symm D)).val
    rw [AddEquiv.apply_symm_apply]
    exact hD

/-- The actual Picard equivalence induced by the identity on Laurent series. -/
def originalCoefficientPicardEquiv : Pic0 Qbar Fo ≃+ Pic0 Qbar FF :=
  QuotientAddGroup.congr _ _ (originalCoefficientDegZeroEquiv N)
    (originalCoefficientDegZero_principal N)

theorem originalCoefficientPicardEquiv_mk (D : Divisor.degZero (K := Qbar) (F := Fo)) :
    originalCoefficientPicardEquiv N (Pic0.mk D) =
      Pic0.mk (originalCoefficientDegZeroEquiv N D) := rfl

theorem originalCoefficientPicardEquiv_torsion (m : ℕ) (x : Pic0 Qbar Fo)
    (hx : x ∈ Pic0.torsion m) : originalCoefficientPicardEquiv N x ∈ Pic0.torsion m := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceFunctionField.GaussReduction
