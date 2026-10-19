import Dubon2026.TameOffDiagonalPowers
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Tame inertia is diagonal in the regular Frobenius basis

Arbitrary-rank adaptation of the ideal-power argument in
anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.lean.
Apache-2.0; retained license: ../../Dependencies/AnthropicFLTReuse/LICENSE.
This discharges a necessary auxiliary local-ring equation for Dubon Theorem 2.6.
-/

namespace Dubon2026
open Matrix IsLocalRing

/-- The tame Frobenius relation forces every off-diagonal inertia entry into
all coefficient-ideal powers and hence to zero in a separated ring. -/
theorem tame_offDiagonal_eq_zero
    {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Ideal A) [IsHausdorff I A] (l : ι → A) (p : ℕ)
    (hu : ∀ i j, i ≠ j → IsUnit (l i - (p : A) * l j))
    (N : Matrix ι ι A) (hN : N - 1 ∈ I.matrix ι)
    (hrel : diagonal l * N = N ^ p * diagonal l) :
    ∀ i j, i ≠ j → N i j = 0 := by
  have hall : ∀ n : ℕ, ∀ i j, i ≠ j → N i j ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro i j hij
      have hp := matrixIdeal_offDiagonal_pow_linear I n N hN ih p i j hij
      have hr := congrArg (fun M : Matrix ι ι A => M i j) hrel
      simp only [diagonal_mul, mul_diagonal] at hr
      have he : (l i - (p : A) * l j) * N i j =
          ((N ^ p) i j - (p : A) * N i j) * l j := by
        rw [sub_mul, hr]
        ring
      apply (Ideal.unit_mul_mem_iff_mem _ (hu i j hij)).mp
      rw [he]
      exact (I ^ (n + 1)).mul_mem_right _ hp
  intro i j hij
  apply IsHausdorff.haus' (I := I) (N i j)
  intro n
  simpa [SModEq.zero] using hall n i j hij

/-- At an auxiliary prime congruent to one in the residue field, regular
residual Frobenius forces residual-unramified tame inertia to be diagonal. -/
theorem regularResidue_tame_diagonal
    {A ι : Type} [CommRing A] [IsLocalRing A]
    [IsHausdorff (maximalIdeal A) A] [Fintype ι] [DecidableEq ι]
    (l : ι → A) (hsep : Function.Injective (fun i => residue A (l i)))
    (p : ℕ) (hp : (p : ResidueField A) = 1)
    (N : Matrix ι ι A) (hN : N.map (residue A) = 1)
    (hrel : diagonal l * N = N ^ p * diagonal l) :
    N = diagonal (fun i => N i i) := by
  have hu (i j : ι) (hij : i ≠ j) : IsUnit (l i - (p : A) * l j) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_sub, map_mul, map_natCast, hp, one_mul]
    exact sub_ne_zero.mpr (fun h => hij (hsep h))
  have hm : N - 1 ∈ (maximalIdeal A).matrix ι := by
    intro i j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residue A (N i j - (1 : Matrix ι ι A) i j) = 0
    have h := congrArg (fun M : Matrix ι ι (ResidueField A) => M i j) hN
    change residue A (N i j) = (1 : Matrix ι ι (ResidueField A)) i j at h
    rw [map_sub, h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hoff := tame_offDiagonal_eq_zero (maximalIdeal A) l p hu N hm hrel
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · rw [hoff i j hij, diagonal_apply_ne _ hij]

end Dubon2026
