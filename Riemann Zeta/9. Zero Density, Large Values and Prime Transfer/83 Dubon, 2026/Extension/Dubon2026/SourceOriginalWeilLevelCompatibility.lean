import Dubon2026.SourceOriginalWeilLevelDatum

/-! DUB-17/18 -> original Tate pairing. The transition between actual
Picard torsion subgroups is multiplication by m, and the divisorial
pairing transition is the m-th power. No compatibility is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- Multiplication by m from actual (n*m)-torsion to actual n-torsion. -/
def originalPicardTorsionLower (n m : ℕ) :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) (n * m) →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n where
  toFun x := ⟨m • x.val, by
    rw [Pic0.mem_torsion_iff, smul_smul]
    exact Pic0.mem_torsion_iff.mp x.property⟩
  map_zero' := Subtype.ext (smul_zero m)
  map_add' x y := Subtype.ext (smul_add m x.val y.val)

theorem originalWeilPairing_level_change [IsAlgClosed L] (n m : ℕ) [NeZero n] [NeZero m]
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) (n * m)) :
    ((originalWeilPairing N L n (originalPicardTorsionLower N L n m x)
      (originalPicardTorsionLower N L n m y) : Lˣ) : L) =
      ((originalWeilPairing N L (n * m) x y : Lˣ) : L) ^ m := by
  obtain ⟨d, rfl, rfl⟩ := exists_original_weil_representative N L (n * m) x y
  have hx : d.lower.classLeft = originalPicardTorsionLower N L n m d.classLeft :=
    Subtype.ext d.lower_classLeft
  have hy : d.lower.classRight = originalPicardTorsionLower N L n m d.classRight :=
    Subtype.ext d.lower_classRight
  rw [← hx, ← hy, originalWeilPairing_eq_pairing, originalWeilPairing_eq_pairing, d.lower_pairing]

end
end Dubon2026.SourceFunctionField
