import Dubon2026.SourceOriginalWeilCommonRepresentatives

/-! DUB-17/18 -> original Tate pairing -> bilinearity of the actual
root-valued Picard pairing. The common representatives are constructed,
and the multiplication law is the proved literal divisor evaluation law. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]

theorem originalWeilPairing_add_left
    (x x' y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n (x + x') y =
      originalWeilPairing N L n x y * originalWeilPairing N L n x' y := by
  obtain ⟨d, d', hD, hf, hx, hx', hy, hy'⟩ := exists_original_weil_common_right N L n x x' y
  have he := originalWeilPairing_eq_pairing N L n (d.addLeft d' hD)
  rw [OriginalWeilDatum.classLeft_addLeft, OriginalWeilDatum.classRight_addLeft,
    d.addLeft_pairing d' hD hf, hx, hx', hy] at he
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [he, ← originalWeilPairing_eq_pairing N L n d,
    ← originalWeilPairing_eq_pairing N L n d', hx, hx', hy, hy']

theorem originalWeilPairing_add_right
    (x y y' : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n x (y + y') =
      originalWeilPairing N L n x y * originalWeilPairing N L n x y' := by
  rw [originalWeilPairing_symm N L n (y + y') x, originalWeilPairing_add_left,
    mul_inv, originalWeilPairing_symm N L n x y,
    originalWeilPairing_symm N L n x y', inv_inv, inv_inv]

theorem originalWeilPairing_zero_left
    (y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n 0 y = 1 := by
  have h := originalWeilPairing_add_left N L n 0 0 y
  rw [zero_add] at h
  exact (mul_eq_left.mp h.symm)

theorem originalWeilPairing_zero_right
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n x 0 = 1 := by
  rw [originalWeilPairing_symm, originalWeilPairing_zero_left, inv_one]

end
end Dubon2026.SourceFunctionField
