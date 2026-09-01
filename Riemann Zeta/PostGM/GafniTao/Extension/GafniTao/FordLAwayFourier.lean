import GafniTao.FordLDiagonalDeletion

/-!
# Ford Lemma 3.3: the marked-diagonal cardinality bound

The coordinate complement of any `i : Fin k` has cardinality `k-1`.
Orthogonality therefore identifies every away-coordinate solution count with
the common reduced count.  Combined with the deletion injection, this proves
the exact finite inequality `U₀ ≤ k P R` used before Hölder.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

theorem fintype_card_fordLAwayIndex {k : ℕ} (i : Fin k) :
    Fintype.card (FordLAwayIndex i) = k - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun j : Fin k ↦ j = i)]
  simp

theorem fordLAwayPolynomial_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLAwayPolynomialMoment (P := P) (p := p) (r := r) Ψ i) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) := by
  calc
    _ = fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^
        Fintype.card (FordLAwayIndex i) :=
      fordCharacterSum_familyMoment_eq_pow_card
        (fordLCoordinateMoment (P := P) (p := p) (r := r) Ψ) α
        |>.trans (by simp [fordLCoordinateWeylSum])
    _ = _ := by rw [fintype_card_fordLAwayIndex]

theorem fordLAwayTotal_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (s Q q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLAwayTotalMoment (P := P) (p := p) (r := r) Ψ i s Q q) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
        (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) := by
  unfold fordLAwayTotalMoment fordCharacterSum
  rw [Fintype.sum_prod_type]
  simp_rw [UnitAddTorus.mFourier_add]
  rw [← Finset.sum_mul_sum]
  change fordCharacterSum
      (fordLAwayPolynomialMoment (P := P) (p := p) (r := r) Ψ i) α *
    fordCharacterSum (fordLPowerPairMoment k Q p q s) α = _
  rw [fordLAwayPolynomial_characterSum, fordLPowerPair_characterSum]

theorem fordLAway_character_mean_eq_count
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (s Q q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k =
      (Nat.card (FordLAwaySolution (P := P) (p := p) (r := r)
        Ψ i s Q q) : ℂ) := by
  rw [← ford_character_sum_mean_eq_zero_count
    (fordLAwayTotalMoment (P := P) (p := p) (r := r) Ψ i s Q q)]
  apply integral_congr_ae
  filter_upwards [] with α
  exact (fordLAwayTotal_characterSum (P := P) (p := p) (r := r)
    Ψ i s Q q α).symm

theorem fordLAway_card_eq_reduced
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (i : Fin k) (s Q q : ℕ) :
    Nat.card (FordLAwaySolution (P := P) (p := p) (r := r) Ψ i s Q q) =
      fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q := by
  exact_mod_cast (fordLAway_character_mean_eq_count
    (P := P) (p := p) (r := r) Ψ i s Q q |>.symm.trans
      (fordLReduced_character_mean_eq_count
        (P := P) (p := p) (r := r) Ψ s Q q))

theorem fordL_marked_card_le
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    Nat.card (FordLMarkedDiagonalSolution Ψ s P Q p q r) ≤
      k * P * fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q := by
  calc
    Nat.card (FordLMarkedDiagonalSolution Ψ s P Q p q r) ≤
        Nat.card (Σ i : Fin k,
          Fin P × FordLAwaySolution (P := P) (p := p) (r := r)
            Ψ i s Q q) :=
      Nat.card_le_card_of_injective _
        (fordLMarkedToAway_injective Ψ s P Q p q r)
    _ = ∑ i : Fin k, Nat.card
          (Fin P × FordLAwaySolution (P := P) (p := p) (r := r)
            Ψ i s Q q) := Nat.card_sigma
    _ = ∑ _i : Fin k,
          P * fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.card_prod, fordLAway_card_eq_reduced]
      simp [Nat.card_eq_fintype_card]
    _ = k * P * fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q := by
      simp [mul_assoc]

theorem fordL_diagonal_le_k_mul_P_mul_reduced
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLDiagonalCount Ψ s P Q p q r ≤
      k * P * fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q :=
  (fordL_diagonal_le_marked Ψ s P Q p q r).trans
    (fordL_marked_card_le Ψ s P Q p q r)

#print axioms fordLAway_character_mean_eq_count
#print axioms fordLAway_card_eq_reduced
#print axioms fordL_marked_card_le
#print axioms fordL_diagonal_le_k_mul_P_mul_reduced

end

end GafniTao
