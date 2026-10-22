import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! DUB-17/18 -> original torsion cardinality -> actual Picard-period comparison.
Transport the annihilator of an integer across the proved additive equivalence.
The native subtype equivalence avoids rebuilding a torsion map and its inverse.
-/
namespace Dubon2026.ComplexLatticeTorsion
noncomputable section

theorem natCard_torsionBy_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (m : ℤ) :
    Nat.card (Submodule.torsionBy ℤ A m) = Nat.card (Submodule.torsionBy ℤ B m) := by
  apply Nat.card_congr (e.toEquiv.subtypeEquiv ?_)
  intro x
  change m • x = 0 ↔ m • e x = 0
  constructor
  · intro h
    rw [← map_zsmul, h, map_zero]
  · intro h
    apply e.injective
    simpa only [map_zsmul, map_zero] using h

end
end Dubon2026.ComplexLatticeTorsion
