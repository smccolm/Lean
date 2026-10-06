import Dubon2026.IsolatedHaarLower

/-! # Exact adapters from natural-number prime blocks to the actual torus coordinates -/

namespace Dubon2026

noncomputable section

/-- Select the actual prime coordinates whose natural indices lie in the given block. -/
def selectedPrimeCoordinates (N : ℕ) (Q : Finset ℕ) : Finset (PrimeCoordinate N) :=
  Finset.univ.filter (fun p => p.val ∈ Q)

theorem mem_selectedPrimeCoordinates {N : ℕ} {Q : Finset ℕ} {p : PrimeCoordinate N} :
    p ∈ selectedPrimeCoordinates N Q ↔ p.val ∈ Q := by
  simp [selectedPrimeCoordinates]

/-- The exact index equivalence; no additional or omitted prime coordinates. -/
def primeSelectionEquiv (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ p ≤ N) : ↥(selectedPrimeCoordinates N Q) ≃ ↥Q where
  toFun p := ⟨p.val.val, mem_selectedPrimeCoordinates.mp p.property⟩
  invFun q := ⟨⟨q.val, mem_primesUpTo.mpr (hQ q.val q.property)⟩,
    mem_selectedPrimeCoordinates.mpr q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_selectedPrimeCoordinates (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ p ≤ N) :
    Fintype.card ↥(selectedPrimeCoordinates N Q) = Q.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (primeSelectionEquiv N Q hQ)

theorem sum_selectedPrimeCoordinates {M : Type*} [AddCommMonoid M]
    (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Nat.Prime p ∧ p ≤ N) (f : ℕ → M) :
    (∑ p : ↥(selectedPrimeCoordinates N Q), f p.val.val) = ∑ p ∈ Q, f p := by
  rw [← Finset.sum_coe_sort Q]
  exact (primeSelectionEquiv N Q hQ).sum_comp (fun p : ↥Q => f p.val)

theorem steinhaus_max_min_le_of_pairwise {κ : Type*} [Fintype κ] [Nonempty κ]
    (b : κ → ℝ) {K : ℝ} (hcomp : ∀ i j, b i / b j ≤ K) :
    steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty b
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty b
  change Finset.univ.sup' Finset.univ_nonempty b / Finset.univ.inf' Finset.univ_nonempty b ≤ K
  rw [hi, hj]
  exact hcomp i j

end

end Dubon2026
