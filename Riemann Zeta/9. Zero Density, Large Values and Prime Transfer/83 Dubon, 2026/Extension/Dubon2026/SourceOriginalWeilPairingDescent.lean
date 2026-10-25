import Dubon2026.SourceOriginalWeilClassInvariance
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! DUB-17/18 -> Frobenius determinant -> original Tate pairing.
The divisorial ratio descends to the actual Picard torsion classes and
takes values in actual roots of unity. The evaluation theorem proves
independence of the chosen representatives. Nondegeneracy and Hecke
adjointness are still separate obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]

/-- The actual divisorial Weil pairing on original Picard torsion classes. -/
def originalWeilPairing
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) : rootsOfUnity n L :=
  let d := (exists_original_weil_representative N L n x y).choose
  rootsOfUnity.mkOfPowEq d.pairing d.pairing_pow_eq_one

theorem originalWeilPairing_eq_pairing (d : OriginalWeilDatum N L n) :
    ((originalWeilPairing N L n d.classLeft d.classRight : Lˣ) : L) = d.pairing := by
  let h := exists_original_weil_representative N L n d.classLeft d.classRight
  change h.choose.pairing = d.pairing
  exact d.pairing_eq_of_classes_eq h.choose h.choose_spec.1 h.choose_spec.2

theorem originalWeilPairing_symm
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n y x = (originalWeilPairing N L n x y)⁻¹ := by
  obtain ⟨d, hx, hy⟩ := exists_original_weil_representative N L n x y
  have hs₁ : d.symm.classLeft = d.classRight := rfl
  have hs₂ : d.symm.classRight = d.classLeft := rfl
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  have he := originalWeilPairing_eq_pairing N L n d.symm
  rw [hs₁, hs₂] at he
  rw [← hx, ← hy, he, originalWeilPairing_eq_pairing, d.symm_pairing]

end
end Dubon2026.SourceFunctionField
