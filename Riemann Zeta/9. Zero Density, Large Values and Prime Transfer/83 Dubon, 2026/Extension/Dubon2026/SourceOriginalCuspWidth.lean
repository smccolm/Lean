import Dubon2026.SourceOriginalSlotWidth

/-! DUB-17/18 -> numerical modular genus -> cusp count. Every actual
primitive triangular conjugate produces a genuine place above infinity
whose j-pole order is exactly (N/a)/gcd(a,N/a). The actual embedding and
the normalization law for every field element are retained for the
remaining equality and exhaustiveness argument. No width is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux

theorem original_cusp_place_with_width (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ (ι : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L)
      (w : Place L (modularFunctionFieldOver N L)),
      ι (jOver N L) = TS L N 1 ∧ ι (jNOver N L) = slotValue ζ s.1 s.2 ∧
      (∀ f, w.ord f * ((s.1 * Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) = (ι f).order) ∧
      w.ord (jOver N L) = -((N / s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) ∧
      w.ord (jNOver N L) = -((s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) := by
  haveI : NeZero s.1 := ⟨index_fst_ne_zero hs⟩
  have ha : s.1 ∣ N := ((mem_indices N s.1 s.2).mp hs).1
  obtain ⟨ι, w, γ, hj, hjN, hγ, hw, _⟩ := original_slot_place N L ζ hζ s hs
  obtain ⟨he, hjw, hjNw⟩ := original_slot_width N L ζ s.1 s.2 ha ι hj hjN w γ hγ hw
  rw [he] at hw
  exact ⟨ι, w, hj, hjN, hw, hjw, hjNw⟩

end
end Dubon2026.SourceFunctionField
