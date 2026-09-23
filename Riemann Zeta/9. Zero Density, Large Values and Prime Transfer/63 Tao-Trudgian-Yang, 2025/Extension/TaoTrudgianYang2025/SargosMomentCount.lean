import TaoTrudgianYang2025.SargosMomentTuples

/-! Literal higher-moment near counts and the exact physical-window upper bound. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosMomentNearPairs (N p : ℕ) (A B : ℝ) :
    Finset (SargosMomentTuple N p × SargosMomentTuple N p) :=
  sargosNearPairs Finset.univ sargosTupleSquareFrequency sargosTupleFourthFrequency A B

def sargosMomentNearCount (N p : ℕ) (δ₁ lambda1 : ℝ) : ℕ :=
  (sargosMomentNearPairs N p (δ₁*(N : ℝ)^2) (lambda1*(N : ℝ)^4)).card

theorem mem_sargosMomentNearPairs {N p : ℕ} {A B : ℝ}
    (t : SargosMomentTuple N p × SargosMomentTuple N p) :
    t ∈ sargosMomentNearPairs N p A B ↔
      |sargosTupleSquareFrequency t.1-sargosTupleSquareFrequency t.2| ≤ A ∧
      |sargosTupleFourthFrequency t.1-sargosTupleFourthFrequency t.2| ≤ B := by
  simp [sargosMomentNearPairs,sargosNearPairs]

theorem sargosMomentNearPairs_mono (N p : ℕ) {A B A' B' : ℝ}
    (hA : A ≤ A') (hB : B ≤ B') :
    sargosMomentNearPairs N p A B ⊆ sargosMomentNearPairs N p A' B' := by
  intro t ht
  rw [mem_sargosMomentNearPairs] at ht ⊢
  exact ⟨ht.1.trans hA,ht.2.trans hB⟩

theorem sargosMomentNearCount_physical {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) {δ lambda : ℝ} (hδ : 0 < δ) (hlambda : 0 < lambda) :
    sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) =
      (sargosMomentNearPairs N p (1/δ) (1/lambda)).card := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he2 : (1/(δ*(N : ℝ)^2))*(N : ℝ)^2 = 1/δ := by field_simp
  have he4 : (1/(lambda*(N : ℝ)^4))*(N : ℝ)^4 = 1/lambda := by field_simp
  rw [sargosMomentNearCount,he2,he4]

theorem sargosMomentNearCount_window_mono {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) {Δ δ μ lambda : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda) :
    sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) ≤
      sargosMomentNearCount N p (1/(Δ*(N : ℝ)^2)) (1/(μ*(N : ℝ)^4)) := by
  rw [sargosMomentNearCount_physical hN p (hΔ.trans_le hδ) (hμ.trans_le hlambda),
    sargosMomentNearCount_physical hN p hΔ hμ]
  apply Finset.card_le_card
  exact sargosMomentNearPairs_mono N p
    (one_div_le_one_div_of_le hΔ hδ) (one_div_le_one_div_of_le hμ hlambda)

theorem sargosQuartic_even_moment_window_le_count {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (z : ℤ → ℂ) (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {δ lambda : ℝ} (hδ : 0 < δ) (hlambda : 0 < lambda) (c d : ℝ) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      ‖sargosQuarticSum N z α γ‖^(2*p)) ≤
      (16*δ*lambda)*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) := by
  rw [sargosMomentNearCount_physical hN p hδ hlambda]
  simp_rw [sargosQuarticSum_norm_even_eq_tuple_norm_sq]
  exact sargosPlanar_window_le_nearPairs
    (Finset.univ : Finset (SargosMomentTuple N p))
    (sargosTupleCoefficient z) sargosTupleSquareFrequency sargosTupleFourthFrequency
    (fun t ht => sargosTupleCoefficient_norm_le_one hz t) hδ hlambda c d

end TaoTrudgianYang2025
