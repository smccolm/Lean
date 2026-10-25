import Dubon2026.SourceOriginalClosedPrescribedOrders
import Dubon2026.SourceOriginalPicardGroup

/-! DUB-17/18 -> original Weil pairing descent -> independent divisor
representatives of actual arithmetic Picard classes. Subtract an actual
principal divisor with the prescribed orders on a finite forbidden set.
The existing quotient and principal-degree theorem preserve the class. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalPic0_representative_avoiding
    (x : Pic0 L (modularFunctionFieldOver N L))
    (S : Finset (Place L (modularFunctionFieldOver N L))) :
    ∃ D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L),
      Pic0.mk D = x ∧ ∀ v ∈ S, D.val v = 0 := by
  obtain ⟨D, hD⟩ := Pic0.mk_surjective x
  obtain ⟨f, hf, hord⟩ := exists_original_closed_prescribed_place_orders N L S D.val
  let P : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L) :=
    ⟨originalPrincipalDivisor N L f, degree_originalPrincipalDivisor N L f⟩
  refine ⟨D - P, ?_, ?_⟩
  · rw [map_sub, originalPic0_principal_eq_zero N L f hf, sub_zero, hD]
  · intro v hv
    change D.val v - v.ord f = 0
    rw [hord v hv, sub_self]

end
end Dubon2026.SourceFunctionField
