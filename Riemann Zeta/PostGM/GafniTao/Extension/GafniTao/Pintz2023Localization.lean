import GafniTao.Pintz2023Polynomial

/-!
# Pintz (2023), equations (4.13)--(4.15): exact dyadic localization

This file localizes the actual coefficient

`a n = sum_{d | n, d <= X} mu(d)`

on the half-open source interval `(X,Y]`.  The real part of the zero is
retained in the coefficient, and the extension to a power-of-two interval is
by literal zero padding.  The final theorem chooses one common dyadic block
on a subset of ordinates; it does not replace the source polynomial by the
bare Moebius mollifier.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The exact finite polynomial produced by Pintz's equation (4.12), after
restricting the coefficient from equation (4.1) to `(X,Y]`. -/
noncomputable def pintz2023TruncatedPolynomial
    (X Y : ℕ) (beta t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X Y,
    pintz2023Coeff X n * (n : ℂ) ^ (-(beta : ℂ)) *
      (n : ℂ) ^ (-(t : ℂ) * I)

/-- Coefficients used to zero-pad the source interval before dyadic
pigeonholing. -/
noncomputable def pintz2023LocalizedLineCoeff
    (X Y : ℕ) (beta : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc X Y then
    pintz2023Coeff X n * (n : ℂ) ^ (-(beta : ℂ))
  else 0

/-- A positive dyadic depth whose power-of-two cover contains every natural
number at most `Y`.  The extra block makes the depth positive even at the
small endpoint. -/
def pintz2023DyadicDepth (Y : ℕ) : ℕ :=
  Nat.clog 2 Y + 1

theorem pintz2023DyadicDepth_pos (Y : ℕ) :
    0 < pintz2023DyadicDepth Y := by
  unfold pintz2023DyadicDepth
  omega

theorem pintz2023_dyadic_cover
    {X Y : ℕ} (hX : 1 ≤ X) :
    Y ≤ 2 ^ pintz2023DyadicDepth Y * X := by
  have hPow : Y ≤ 2 ^ Nat.clog 2 Y :=
    Nat.le_pow_clog (by omega) Y
  have hStep : 2 ^ Nat.clog 2 Y ≤
      2 ^ (Nat.clog 2 Y + 1) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc
    Y ≤ 2 ^ Nat.clog 2 Y := hPow
    _ ≤ 2 ^ (Nat.clog 2 Y + 1) := hStep
    _ ≤ 2 ^ (Nat.clog 2 Y + 1) * X := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ (Nat.clog 2 Y + 1)) hX
    _ = 2 ^ pintz2023DyadicDepth Y * X := by
      rfl

/-- The source interval polynomial is exactly one zero-padded wide
Dirichlet polynomial. -/
theorem pintz2023_truncated_eq_wide
    {X Y : ℕ} (beta t : ℝ) (hX : 1 ≤ X) :
    pintz2023TruncatedPolynomial X Y beta t =
      wideDirichletPoly X (pintz2023DyadicDepth Y)
        (pintz2023LocalizedLineCoeff X Y beta) t := by
  classical
  have hSubset : Finset.Ioc X Y ⊆
      Finset.Ioc X (2 ^ pintz2023DyadicDepth Y * X) := by
    intro n hn
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1,
        (Finset.mem_Ioc.mp hn).2.trans (pintz2023_dyadic_cover hX)⟩
  unfold pintz2023TruncatedPolynomial wideDirichletPoly
    pintz2023LocalizedLineCoeff
  calc
    ∑ n ∈ Finset.Ioc X Y,
        pintz2023Coeff X n * (n : ℂ) ^ (-(beta : ℂ)) *
          (n : ℂ) ^ (-(t : ℂ) * I) =
      ∑ n ∈ Finset.Ioc X Y,
        (if n ∈ Finset.Ioc X Y then
          pintz2023Coeff X n * (n : ℂ) ^ (-(beta : ℂ)) else 0) *
            (n : ℂ) ^ (-(t : ℂ) * I) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [if_pos hn]
    _ = ∑ n ∈ Finset.Ioc X (2 ^ pintz2023DyadicDepth Y * X),
        (if n ∈ Finset.Ioc X Y then
          pintz2023Coeff X n * (n : ℂ) ^ (-(beta : ℂ)) else 0) *
            (n : ℂ) ^ (-(t : ℂ) * I) := by
              apply Finset.sum_subset hSubset
              intro n hnBig hnSmall
              rw [if_neg hnSmall, zero_mul]

/-- The factorized source summand is the literal complex power
`n^(-(beta+i t))`. -/
theorem pintz2023_factorized_term
    {n : ℕ} (hn : 0 < n) (beta t : ℝ) :
    (n : ℂ) ^ (-(beta : ℂ)) *
        (n : ℂ) ^ (-(t : ℂ) * I) =
      (n : ℂ) ^ (-((beta : ℂ) + I * (t : ℂ))) := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  ring

/-- Complex-power form of the exact source polynomial. -/
theorem pintz2023_truncated_eq_complex_power
    {X Y : ℕ} (beta t : ℝ) (hX : 0 < X) :
    pintz2023TruncatedPolynomial X Y beta t =
      ∑ n ∈ Finset.Ioc X Y,
        pintz2023Coeff X n *
          (n : ℂ) ^ (-((beta : ℂ) + I * (t : ℂ))) := by
  unfold pintz2023TruncatedPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := lt_trans hX (Finset.mem_Ioc.mp hn).1
  rw [mul_assoc, pintz2023_factorized_term hnPos]

/-- Exact common-block selection for a finite family of source ordinates.
The chosen coefficient sequence is still the literal zero-padded Pintz
coefficient, so the last dyadic block automatically retains its right-edge
truncation. -/
theorem exists_pintz2023_dyadic_block_and_subset
    {X Y : ℕ} (beta : ℝ) (W : Finset ℝ) (V : ℝ)
    (hX : 1 ≤ X)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y beta t‖) :
    ∃ r ∈ Finset.range (pintz2023DyadicDepth Y), ∃ W' ⊆ W,
      (W.card : ℝ) ≤ pintz2023DyadicDepth Y * (W'.card : ℝ) ∧
      ∀ t ∈ W',
        V / pintz2023DyadicDepth Y ≤
          ‖dirichletPoly (2 ^ r * X)
            (pintz2023LocalizedLineCoeff X Y beta) t‖ := by
  have hWide : ∀ t ∈ W,
      V ≤ ‖wideDirichletPoly X (pintz2023DyadicDepth Y)
        (pintz2023LocalizedLineCoeff X Y beta) t‖ := by
    intro t ht
    rw [← pintz2023_truncated_eq_wide beta t hX]
    exact hLarge t ht
  exact exists_dyadic_block_and_subset X (pintz2023DyadicDepth Y)
    (pintz2023LocalizedLineCoeff X Y beta) W V
    (pintz2023DyadicDepth_pos Y) hWide

#print axioms pintz2023_dyadic_cover
#print axioms pintz2023_truncated_eq_wide
#print axioms pintz2023_truncated_eq_complex_power
#print axioms exists_pintz2023_dyadic_block_and_subset

end

end GafniTao
