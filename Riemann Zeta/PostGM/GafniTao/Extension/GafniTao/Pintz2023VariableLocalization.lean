import GafniTao.Pintz2023IntervalPower
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Pintz (2023), equations (4.12)--(4.16): variable-line localization

The detected zeros in Pintz's argument do not all have the same real part.
This file performs the first common dyadic selection while retaining the
individual exponent `betaAt t`.  The selected finite index set is literal:
it is the intersection of the chosen dyadic block with the truncated source
interval `(X,Y]`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal, possibly right-truncated, source block selected at depth
`r`. -/
def pintz2023LocalizedInterval (X Y r : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 ^ r * X) (2 * (2 ^ r * X))).filter
    (fun n => n ∈ Finset.Ioc X Y)

theorem pintz2023LocalizedInterval_subset_dyadic
    (X Y r : ℕ) :
    pintz2023LocalizedInterval X Y r ⊆
      Finset.Ioc (2 ^ r * X) (2 * (2 ^ r * X)) :=
  Finset.filter_subset _ _

/-- A zero-padded dyadic polynomial is exactly the source polynomial on the
literal truncated block. -/
theorem dirichletPoly_pintz2023LocalizedLineCoeff_eq_intervalBlock
    (X Y r : ℕ) (beta gamma : ℝ) :
    dirichletPoly (2 ^ r * X)
        (pintz2023LocalizedLineCoeff X Y beta) gamma =
      pintz2023IntervalBlock X (pintz2023LocalizedInterval X Y r)
        ((beta : ℂ) + I * (gamma : ℂ)) := by
  classical
  let S := Finset.Ioc (2 ^ r * X) (2 * (2 ^ r * X))
  let P := Finset.Ioc X Y
  let f : ℕ → ℂ := fun n =>
    pintz2023Coeff X n * (n : ℂ) ^
      (-((beta : ℂ) + I * (gamma : ℂ)))
  have hterm : ∀ n ∈ S,
      pintz2023LocalizedLineCoeff X Y beta n *
          (n : ℂ) ^ (-(gamma : ℂ) * I) =
        if n ∈ P then f n else 0 := by
    intro n hn
    by_cases hnP : n ∈ P
    · rw [if_pos hnP]
      unfold pintz2023LocalizedLineCoeff
      rw [if_pos hnP]
      have hnPos : 0 < n := by
        have hXn := (Finset.mem_Ioc.mp hnP).1
        omega
      dsimp only [f]
      rw [mul_assoc, pintz2023_factorized_term hnPos]
    · rw [if_neg hnP]
      unfold pintz2023LocalizedLineCoeff
      rw [if_neg hnP, zero_mul]
  calc
    dirichletPoly (2 ^ r * X)
        (pintz2023LocalizedLineCoeff X Y beta) gamma =
      ∑ n ∈ S,
        pintz2023LocalizedLineCoeff X Y beta n *
          (n : ℂ) ^ (-(gamma : ℂ) * I) := by rfl
    _ = ∑ n ∈ S, if n ∈ P then f n else 0 :=
      Finset.sum_congr rfl hterm
    _ = ∑ n ∈ S.filter (fun n => n ∈ P), f n :=
      (Finset.sum_filter (fun n => n ∈ P) f).symm
    _ = pintz2023IntervalBlock X (pintz2023LocalizedInterval X Y r)
        ((beta : ℂ) + I * (gamma : ℂ)) := by
      dsimp only [S, P, f]
      unfold pintz2023IntervalBlock pintz2023LocalizedInterval
      apply Finset.sum_congr rfl
      intro n hn
      rfl

/-- Simultaneous first-block selection with the individual detected real
parts retained.  This is the source-faithful replacement for applying a
fixed-line coefficient theorem to the whole zero family. -/
theorem exists_pintz2023_variable_dyadic_block_and_subset
    {X Y : ℕ} (W : Finset ℝ) (V : ℝ)
    (betaAt gammaAt : ℝ → ℝ)
    (hX : 1 ≤ X)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y (betaAt t) (gammaAt t)‖) :
    ∃ r ∈ Finset.range (pintz2023DyadicDepth Y), ∃ W' ⊆ W,
      (W.card : ℝ) ≤ pintz2023DyadicDepth Y * (W'.card : ℝ) ∧
      ∀ t ∈ W',
        V / pintz2023DyadicDepth Y ≤
          ‖pintz2023IntervalBlock X
            (pintz2023LocalizedInterval X Y r)
            (((betaAt t : ℝ) : ℂ) + I * (((gammaAt t : ℝ) : ℂ)))‖ := by
  classical
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range (pintz2023DyadicDepth Y),
      V / pintz2023DyadicDepth Y ≤
        ‖dirichletPoly (2 ^ r * X)
          (pintz2023LocalizedLineCoeff X Y (betaAt t)) (gammaAt t)‖ := by
    intro t ht
    have hWide : V ≤
        ‖wideDirichletPoly X (pintz2023DyadicDepth Y)
          (pintz2023LocalizedLineCoeff X Y (betaAt t)) (gammaAt t)‖ := by
      rw [← pintz2023_truncated_eq_wide (betaAt t) (gammaAt t) hX]
      exact hLarge t ht
    exact exists_large_dyadic_block X (pintz2023DyadicDepth Y)
      (pintz2023LocalizedLineCoeff X Y (betaAt t)) (gammaAt t) V
      (pintz2023DyadicDepth_pos Y) hWide
  let index (t : ℝ) : ℕ :=
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hIndexMem : ∀ t ∈ W,
      index t ∈ Finset.range (pintz2023DyadicDepth Y) := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hIndexLarge : ∀ t ∈ W,
      V / pintz2023DyadicDepth Y ≤
        ‖dirichletPoly (2 ^ index t * X)
          (pintz2023LocalizedLineCoeff X Y (betaAt t)) (gammaAt t)‖ := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).2
  have hCard : W.card = ∑ r ∈ Finset.range (pintz2023DyadicDepth Y),
      (W.filter fun t => index t = r).card :=
    Finset.card_eq_sum_card_fiberwise hIndexMem
  have hCardReal : (W.card : ℝ) =
      ∑ r ∈ Finset.range (pintz2023DyadicDepth Y),
        ((W.filter fun t => index t = r).card : ℝ) := by
    exact_mod_cast hCard
  obtain ⟨r, hr, hrLarge⟩ := pigeonhole_real_sum
    (pintz2023DyadicDepth Y)
    (fun q => ((W.filter fun t => index t = q).card : ℝ))
    (W.card : ℝ) (by rw [hCardReal]) (pintz2023DyadicDepth_pos Y)
  refine ⟨r, hr, W.filter fun t => index t = r,
    Finset.filter_subset _ _, ?_, ?_⟩
  · have hDepth : (0 : ℝ) < pintz2023DyadicDepth Y := by
      exact_mod_cast pintz2023DyadicDepth_pos Y
    calc
      (W.card : ℝ) = pintz2023DyadicDepth Y *
          ((W.card : ℝ) / pintz2023DyadicDepth Y) := by field_simp
      _ ≤ pintz2023DyadicDepth Y *
          ((W.filter fun t => index t = r).card : ℝ) := by gcongr
  · intro t ht
    rw [Finset.mem_filter] at ht
    have hBlock := hIndexLarge t ht.1
    rw [ht.2] at hBlock
    simpa only [
      dirichletPoly_pintz2023LocalizedLineCoeff_eq_intervalBlock]
      using hBlock

#print axioms pintz2023LocalizedInterval_subset_dyadic
#print axioms dirichletPoly_pintz2023LocalizedLineCoeff_eq_intervalBlock
#print axioms exists_pintz2023_variable_dyadic_block_and_subset

end

end GafniTao
