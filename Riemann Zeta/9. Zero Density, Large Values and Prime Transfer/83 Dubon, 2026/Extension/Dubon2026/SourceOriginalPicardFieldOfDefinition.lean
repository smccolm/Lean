import Dubon2026.SourceOriginalPlaceFieldOfDefinition
import Dubon2026.SourceOriginalArithmeticPicard
import Mathlib.Algebra.GroupWithZero.Action.End

/-! DUB-17/18 -> continuous original torsion Galois action. A finite
divisor uses finitely many original places, each with a proved finite
field of definition. Their finite compositum fixes the same divisor and
its class. The original arithmetic action therefore has open stabilizers
on the actual degree-zero divisor-class group.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

/-- The literal original Pic0 representation as the native arithmetic group action. -/
instance originalJZeroArithmeticAction (N : ℕ) [NeZero N] :
    DistribMulAction (Qbar ≃ₐ[ℚ] Qbar) (originalJZero N) :=
  DistribMulAction.compHom _ (originalArithmeticPicardRep N (L := Qbar))

private theorem divisor_fixed_of_support_fixed (N : ℕ) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (D : Divisor Qbar (modularFunctionFieldOver N Qbar))
    (hD : ∀ v ∈ D.support, originalArithmeticPlace N σ v = v) :
    originalArithmeticDivisorEquiv N σ D = D := by
  classical
  conv_lhs => rw [← D.sum_single]
  rw [map_finsuppSum]
  calc
    D.sum (fun v n => originalArithmeticDivisorEquiv N σ (Finsupp.single v n)) =
        D.sum (fun v n => Finsupp.single v n) := by
      apply Finsupp.sum_congr
      intro v hv
      change Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N σ) (Finsupp.single v (D v)) = _
      rw [Finsupp.equivMapDomain_single]
      change Finsupp.single (originalArithmeticPlace N σ v) (D v) = _
      rw [hD v hv]
    _ = D := D.sum_single

theorem original_picard_fieldOfDefinition (N : ℕ) [NeZero N] (x : originalJZero N) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → σ • x = x := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  choose E hE hfix using original_place_fieldOfDefinition N
  letI : ∀ v, FiniteDimensional ℚ (E v) := hE
  refine ⟨⨆ v ∈ D.val.support, E v, IntermediateField.finiteDimensional_iSup_of_finset, fun σ hσ => ?_⟩
  have hD : originalArithmeticDivisorEquiv N σ D.val = D.val := by
    apply divisor_fixed_of_support_fixed
    intro v hv
    exact hfix v σ (IntermediateField.fixingSubgroup_le (le_iSup₂_of_le v hv le_rfl) hσ)
  change originalArithmeticPicard N σ (Pic0.mk D) = Pic0.mk D
  rw [originalArithmeticPicard_mk]
  exact congrArg Pic0.mk (Subtype.ext hD)

theorem originalJZero_isOpen_stabilizer (N : ℕ) [NeZero N] (x : originalJZero N) :
    IsOpen (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) x : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
  obtain ⟨E, hE, hfix⟩ := original_picard_fieldOfDefinition N x
  letI := hE
  apply Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  exact MulAction.mem_stabilizer_iff.mpr (hfix σ hσ)

end
end Dubon2026.SourceFunctionField
