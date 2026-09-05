import GafniTao.Pintz2023CoefficientSplit
import RiemannZeta.GuthMaynard.DFIDelta

/-!
# Pintz (2023), equation (4.14): exact divisor-pair reindexing

The large-`m` coefficient block is regrouped as a finite rectangle in the
Möbius divisor `d` and complementary factor `m`.  Endpoint and zero-index
conventions are explicit; terms outside the source interval vanish rather
than being silently discarded.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The finite rectangular `d,m` sum obtained from the large-`m` part of
Pintz (4.13).  The enclosing range `1 <= d,m <= Y+1` is harmless because
the literal source membership condition forces `d*m <= Y`. -/
noncomputable def pintz2023LargeMRectangleBlock
    (X Y : ℕ) (Iset : Finset ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (Y + 1),
    ∑ m ∈ Finset.Icc 1 (Y + 1),
      if d ≤ X ∧ d * m ∈ Iset ∧ R < (m : ℝ) then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (d * m : ℂ) ^ (-s)
      else 0

/-- Each divisor antidiagonal inside the source interval recovers exactly
the corresponding large-`m` coefficient term. -/
theorem pintz2023_largeM_antidiagonal_term
    {X k : ℕ} {Iset : Finset ℕ} {R : ℝ} {s : ℂ}
    (hk : k ∈ Iset) :
    (∑ p ∈ k.divisorsAntidiagonal,
      if p.1 ≤ X ∧ p.1 * p.2 ∈ Iset ∧ R < (p.2 : ℝ) then
        ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) *
          (p.1 * p.2 : ℂ) ^ (-s)
      else 0) =
      pintz2023LargeMCoeff X k R * (k : ℂ) ^ (-s) := by
  classical
  rw [pintz2023LargeMCoeff_eq_antidiagonal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hcond : p.1 ≤ X ∧ R < (p.2 : ℝ)
  · rw [if_pos hcond]
    have hmem : p.1 * p.2 ∈ Iset := hprod.symm ▸ hk
    rw [if_pos ⟨hcond.1, hmem, hcond.2⟩]
    have hprodC : (p.1 : ℂ) * (p.2 : ℂ) = (k : ℂ) := by
      exact_mod_cast hprod
    rw [hprodC]
  · rw [if_neg hcond]
    have hnot : ¬(p.1 ≤ X ∧ p.1 * p.2 ∈ Iset ∧ R < (p.2 : ℝ)) := by
      intro h
      exact hcond ⟨h.1, h.2.2⟩
    rw [if_neg hnot, zero_mul]

/-- For a product not in the source interval, the whole divisor
antidiagonal contributes zero. -/
theorem pintz2023_largeM_antidiagonal_term_of_not_mem
    {X k : ℕ} {Iset : Finset ℕ} {R : ℝ} {s : ℂ}
    (hk : k ∉ Iset) :
    (∑ p ∈ k.divisorsAntidiagonal,
      if p.1 ≤ X ∧ p.1 * p.2 ∈ Iset ∧ R < (p.2 : ℝ) then
        ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) *
          (p.1 * p.2 : ℂ) ^ (-s)
      else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [if_neg]
  intro h
  exact hk (hprod ▸ h.2.1)

/-- Exact equation-(4.14) reindexing before any analytic estimate. -/
theorem pintz2023SplitLargeM_eq_rectangle
    {X Y : ℕ} {Iset : Finset ℕ} {R : ℝ} {s : ℂ}
    (hIset : Iset ⊆ Finset.Ioc 0 Y) :
    pintz2023SplitIntervalBlock
        (fun n => pintz2023LargeMCoeff X n R) Iset s =
      pintz2023LargeMRectangleBlock X Y Iset R s := by
  classical
  let F : ℕ × ℕ → ℂ := fun p =>
    if p.1 ≤ X ∧ p.1 * p.2 ∈ Iset ∧ R < (p.2 : ℝ) then
      ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) *
        (p.1 * p.2 : ℂ) ^ (-s)
    else 0
  have hzero : ∀ p ∈
      (Finset.Icc 1 (Y + 1)) ×ˢ (Finset.Icc 1 (Y + 1)),
      ¬p.1 * p.2 < Y + 1 → F p = 0 := by
    intro p hp hnot
    dsimp only [F]
    rw [if_neg]
    intro h
    have hprodY := (Finset.mem_Ioc.mp (hIset h.2.1)).2
    omega
  have hRegroup := dfiSum_product_eq_sum_divisorsAntidiagonal
    (Y + 1) F hzero
  have hSubset : Iset ⊆ Finset.Ico 1 (Y + 1) := by
    intro k hk
    have hkRange := Finset.mem_Ioc.mp (hIset hk)
    rw [Finset.mem_Ico]
    omega
  have hOuter :
      ∑ k ∈ Finset.Ico 1 (Y + 1),
          ∑ p ∈ k.divisorsAntidiagonal, F p =
        ∑ k ∈ Iset,
          pintz2023LargeMCoeff X k R * (k : ℂ) ^ (-s) := by
    have hRestrict :
        (∑ k ∈ Iset, ∑ p ∈ k.divisorsAntidiagonal, F p) =
          ∑ k ∈ Finset.Ico 1 (Y + 1),
            ∑ p ∈ k.divisorsAntidiagonal, F p := by
      apply Finset.sum_subset hSubset
      intro k hkRange hkNot
      simpa only [F] using
        (pintz2023_largeM_antidiagonal_term_of_not_mem
          (X := X) (R := R) (s := s) hkNot)
    calc
      (∑ k ∈ Finset.Ico 1 (Y + 1),
          ∑ p ∈ k.divisorsAntidiagonal, F p) =
          ∑ k ∈ Iset, ∑ p ∈ k.divisorsAntidiagonal, F p := hRestrict.symm
      _ = ∑ k ∈ Iset,
          pintz2023LargeMCoeff X k R * (k : ℂ) ^ (-s) := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [F] using
          (pintz2023_largeM_antidiagonal_term
            (X := X) (R := R) (s := s) hk)
  unfold pintz2023SplitIntervalBlock pintz2023LargeMRectangleBlock
  change (∑ k ∈ Iset,
      pintz2023LargeMCoeff X k R * (k : ℂ) ^ (-s)) = _
  rw [← hOuter, ← hRegroup]

#print axioms pintz2023_largeM_antidiagonal_term
#print axioms pintz2023_largeM_antidiagonal_term_of_not_mem
#print axioms pintz2023SplitLargeM_eq_rectangle

end

end GafniTao
