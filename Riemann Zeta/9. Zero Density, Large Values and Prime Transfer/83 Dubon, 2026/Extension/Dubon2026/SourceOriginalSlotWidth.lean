import Dubon2026.SourceOriginalSlotRange

/-! DUB-17/18 -> numerical modular genus -> exact cusp widths. The actual
images of j and j_N force the normalization factor to divide gcd(N,a^2).
The proved expansion range forces the reverse divisibility by evaluating
an actual uniformizer. Thus the normalization is a*gcd(a,N/a), and the
two normalized pole orders are derived exactly. This is the selected
slotWidth argument from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, adapted to the proved
original embeddings and native integer-valued place construction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux

theorem original_slot_width (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L]
    (ζ : Lˣ) (a b : ℕ) [NeZero a] (ha : a ∣ N)
    (ι : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L)
    (hj : ι (jOver N L) = TS L N 1) (hjN : ι (jNOver N L) = slotValue ζ a b)
    (w : Place L (modularFunctionFieldOver N L)) (γ : ℕ) (hγ : 0 < γ)
    (hw : ∀ f, w.ord f * (γ : ℤ) = (ι f).order) :
    γ = a * Nat.gcd a (N / a) ∧
      w.ord (jOver N L) = -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
      w.ord (jNOver N L) = -((a / Nat.gcd a (N / a) : ℕ) : ℤ) := by
  let g := Nat.gcd a (N / a)
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left (NeZero.ne a)
  haveI : NeZero (a * g) := ⟨Nat.mul_ne_zero (NeZero.ne a) hg0⟩
  have hdN : a * g ∣ N :=
    (Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)).trans (by rw [Nat.mul_div_cancel' ha])
  have h1 : w.ord (jOver N L) * (γ : ℤ) = -(N : ℤ) := by
    rw [hw, hj, laurent_order_TS]
  have h2 : w.ord (jNOver N L) * (γ : ℤ) = -((a * a : ℕ) : ℤ) := by
    rw [hw, hjN, slotValue_eq, laurent_order_TS]
  have hγdvd : (γ : ℤ) ∣ ((a * g : ℕ) : ℤ) := by
    have hN : (γ : ℤ) ∣ (N : ℤ) :=
      ⟨-w.ord (jOver N L), by rw [mul_neg, mul_comm (γ : ℤ), h1, neg_neg]⟩
    have haa : (γ : ℤ) ∣ ((a * a : ℕ) : ℤ) :=
      ⟨-w.ord (jNOver N L), by rw [mul_neg, mul_comm (γ : ℤ), h2, neg_neg]⟩
    have he : Nat.gcd N (a * a) = a * g := by
      conv_lhs => rw [← Nat.mul_div_cancel' ha]
      rw [Nat.gcd_mul_left, Nat.gcd_comm]
    rw [← he, Nat.gcd_eq_gcd_ab]
    exact dvd_add (Dvd.dvd.mul_right hN _) (Dvd.dvd.mul_right haa _)
  obtain ⟨f, hf⟩ := original_slot_embedding_range L N ζ a b ha ι hj hjN w.uniformizer
  have heγ : (γ : ℤ) = (ι w.uniformizer).order := by
    have h := hw w.uniformizer
    rw [w.ord_uniformizer, one_mul] at h
    exact h
  have hgdvd : ((a * g : ℕ) : ℤ) ∣ (γ : ℤ) := by
    rw [heγ, ← hf]
    change ((a * g : ℕ) : ℤ) ∣ (qExpand L (a * g) f).order
    rw [laurent_order_qExpand]
    exact dvd_mul_right _ _
  have hgpos : (0 : ℤ) < ((a * g : ℕ) : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (a * g))
  have hγz : (0 : ℤ) < γ := by exact_mod_cast hγ
  have he : (γ : ℤ) = ((a * g : ℕ) : ℤ) := Int.dvd_antisymm hγz.le hgpos.le hγdvd hgdvd
  refine ⟨by exact_mod_cast he, ?_, ?_⟩
  · have hdiv : (N / a / g) * (a * g) = N := by
      rw [Nat.div_div_eq_div_mul, Nat.div_mul_cancel hdN]
    have hk : (-((N / a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -(N : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ hgpos.ne' ((he ▸ h1).trans hk.symm)
  · have hdiv : (a / g) * (a * g) = a * a := by
      rw [mul_comm a g, ← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left a (N / a))]
    have hk : (-((a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -((a * a : ℕ) : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ hgpos.ne' ((he ▸ h2).trans hk.symm)

end
end Dubon2026.SourceFunctionField
