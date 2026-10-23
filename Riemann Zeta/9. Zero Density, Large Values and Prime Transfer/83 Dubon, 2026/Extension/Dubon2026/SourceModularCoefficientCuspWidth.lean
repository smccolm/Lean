import Dubon2026.SourceModularCoefficientSlotWidth

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> cusp count.
Every actual primitive conjugate gives a coefficient-field place with exact
width (N/a)/gcd(a,N/a) and the proved normalization on every field element.
All embeddings, root identities, generation and order inputs are derived.
Distinctness and exhaustion of these cusp places remain to be proved. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux

theorem coeff_cusp_place_with_width (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [IsAlgClosed L] (hNL : (N : L) ≠ 0)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ (ι : modularFunctionFieldCoeff N L →ₐ[L] LaurentSeries L)
      (w : Place L (modularFunctionFieldCoeff N L)),
      ι (jCoeff N L) = TS L N 1 ∧ ι ((⟨qExpand L N (jqModC L), jqd_mem_coeff_field N L dvd_rfl⟩ : modularFunctionFieldCoeff N L)) = slotValue ζ s.1 s.2 ∧
      (∀ f, w.ord f * ((s.1 * Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) = (ι f).order) ∧
      w.ord (jCoeff N L) = -((N / s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) ∧
      w.ord ((⟨qExpand L N (jqModC L), jqd_mem_coeff_field N L dvd_rfl⟩ : modularFunctionFieldCoeff N L)) = -((s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) := by
  haveI : NeZero s.1 := ⟨index_fst_ne_zero hs⟩
  have ha : s.1 ∣ N := ((mem_indices N s.1 s.2).mp hs).1
  obtain ⟨ι, w, γ, hj, hjN, hγ, hw, _⟩ := coeff_slot_place N L hNL ζ hζ s hs
  obtain ⟨he, hjw, hjNw⟩ := coeff_slot_width N L hNL ζ s.1 s.2 ha ι hj hjN w γ hγ hw
  rw [he] at hw
  exact ⟨ι, w, hj, hjN, hw, hjw, hjNw⟩

end
end Dubon2026.SourceFunctionField
