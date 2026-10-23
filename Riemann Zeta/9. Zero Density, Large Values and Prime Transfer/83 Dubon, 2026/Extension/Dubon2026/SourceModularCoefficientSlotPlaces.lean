import Dubon2026.SourceModularCoefficientSlotEmbedding
import Dubon2026.SourceCurveLaurentPlaces
import Dubon2026.SourceLaurentExpansionOrders

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> cusp count.
Reuse the existing Laurent-order and place-normalization proofs on the
actual coefficient-field embeddings. Each primitive conjugate produces a
genuine place above infinity, with a positive normalization for all orders.
Exact widths, distinctness and exhaustion remain to be proved. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve ConjugateSlots PrimeDegreeAux

/-- Every primitive conjugate produces an actual coefficient-field place above infinity. -/
theorem coeff_slot_place (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] (hNK : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ (ι : modularFunctionFieldCoeff N K →ₐ[K] LaurentSeries K)
      (w : Place K (modularFunctionFieldCoeff N K)) (γ : ℕ),
      ι (jCoeff N K) = TS K N 1 ∧
      ι ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩ = slotValue ζ s.1 s.2 ∧
      0 < γ ∧ (∀ f, w.ord f * (γ : ℤ) = (ι f).order) ∧ w.ord (jCoeff N K) < 0 := by
  obtain ⟨ι, hj, hjN⟩ := coeff_slot_embedding N K hNK ζ hζ s hs
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨w, γ, hγ, hw⟩ := Place.exists_place_of_laurent_embedding ι
    ⟨jCoeff N K, by rw [hj, laurent_order_TS]; omega⟩
  refine ⟨ι, w, γ, hj, hjN, hγ, hw, ?_⟩
  have ho : w.ord (jCoeff N K) * (γ : ℤ) = -(N : ℤ) := by
    rw [hw, hj, laurent_order_TS]
  have hγz : (0 : ℤ) < γ := by exact_mod_cast hγ
  nlinarith

end Dubon2026.SourceFunctionField
