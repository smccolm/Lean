import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sigma

/-! DUB-17/18 -> cover Euler count -> constant finite fibers.
Reuse the native sigma-of-fibers equivalence and finite cardinal sum formula
for the full inverse image of the actual finite base vertex set. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set

theorem card_preimage_of_constant_fibers {X B : Type*} (p : X → B) (S : Set B) [Finite S]
    (d : ℕ) (hf : ∀ v : S, Finite {w : X // p w = v.1})
    (hc : ∀ v : S, Nat.card {w : X // p w = v.1} = d) :
    Nat.card (p ⁻¹' S) = Nat.card S * d := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : ∀ v : S, Finite {w : X // p w = v.1} := hf
  let e := Equiv.sigmaSubtypeFiberEquivSubtype p
    (p := fun w => p w ∈ S) (q := fun v => v ∈ S) (fun _ => Iff.rfl)
  change Nat.card {w : X // p w ∈ S} = Nat.card S * d
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rfl

end
end Dubon2026.SourceFunctionField.SheetCover
