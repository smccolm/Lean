import Dubon2026.SourceCurveLaurentPlaces
import Dubon2026.SourceLaurentExpansionOrders

/-! DUB-17/18 -> numerical modular genus -> cusp classification. Every
primitive triangular conjugate now supplies a genuine place of the
original coefficient-extended field, together with its actual Laurent
embedding and a proved positive integral normalization of every order.
The image of j has order -N, so this place is proved to lie over infinity.
Exact cusp widths and the equality/classification of these places remain.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux

theorem original_slot_place (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ (ι : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L)
      (w : Place L (modularFunctionFieldOver N L)) (γ : ℕ),
      ι (jOver N L) = TS L N 1 ∧ ι (jNOver N L) = slotValue ζ s.1 s.2 ∧
      0 < γ ∧ (∀ f, w.ord f * (γ : ℤ) = (ι f).order) ∧ w.ord (jOver N L) < 0 := by
  obtain ⟨ι, hj, hjN⟩ := original_slot_embedding N L ζ hζ s hs
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨w, γ, hγ, hw⟩ := Place.exists_place_of_laurent_embedding ι
    ⟨jOver N L, by rw [hj, laurent_order_TS]; omega⟩
  refine ⟨ι, w, γ, hj, hjN, hγ, hw, ?_⟩
  have ho : w.ord (jOver N L) * (γ : ℤ) = -(N : ℤ) := by
    rw [hw, hj, laurent_order_TS]
  have hγz : (0 : ℤ) < γ := by exact_mod_cast hγ
  nlinarith

end
end Dubon2026.SourceFunctionField
