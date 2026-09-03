import GafniTao.HeathBrownBlockParameter
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivatives of Heath-Brown's normalized coordinates

These are the calculus bridges that connect the abstract spacing lemmas to
the actual `(k-1)`-st and `(k-2)`-nd derivative coordinates of the source
phase.  Factorials are retained literally.
-/

namespace GafniTao

noncomputable section

theorem deriv_heathBrownDerivativeCoordinate
    (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    deriv (fun y => heathBrownDerivativeCoordinate f j y) x =
      iteratedDeriv (j + 1) f x / (j.factorial : ℝ) := by
  unfold heathBrownDerivativeCoordinate
  rw [deriv_div_const, ← iteratedDeriv_succ]

theorem deriv_heathBrownDerivativeCoordinate_last
    {f : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    deriv (fun y => heathBrownDerivativeCoordinate f (k - 1) y) x =
      iteratedDeriv k f x / ((k - 1).factorial : ℝ) := by
  rw [deriv_heathBrownDerivativeCoordinate]
  congr 2
  omega

theorem heathBrownDerivativeCoordinate_last_lower
    {f : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) {lambda x : ℝ}
    (hlower : lambda ≤ iteratedDeriv k f x) :
    lambda / ((k - 1).factorial : ℝ) ≤
      deriv (fun y => heathBrownDerivativeCoordinate f (k - 1) y) x := by
  rw [deriv_heathBrownDerivativeCoordinate_last hk]
  exact div_le_div_of_nonneg_right hlower (by positivity)

theorem heathBrownDerivativeCoordinate_last_upper
    {f : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) {A lambda x : ℝ}
    (hupper : iteratedDeriv k f x ≤ A * lambda) :
    deriv (fun y => heathBrownDerivativeCoordinate f (k - 1) y) x ≤
      A * lambda / ((k - 1).factorial : ℝ) := by
  rw [deriv_heathBrownDerivativeCoordinate_last hk]
  exact div_le_div_of_nonneg_right hupper (by positivity)

/-- Instantiation of the close-pair lemma with the source value
`mu = lambda/(k-1)!`. -/
theorem heathBrownPairCountTwo_source_separation
    {N k H K : ℕ} {f : ℝ → ℝ} {m n : ℕ} {lambda : ℝ}
    (hk : 1 ≤ k) (hlambda : 0 < lambda)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x)
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H K f)
    (hspread :
      |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤ 1 / 2) :
    |(m : ℝ) - n| ≤
      4 * ((k - 1).factorial : ℝ) /
        (lambda * (H : ℝ) ^ (k - 1)) := by
  have hmuPos : 0 < lambda / ((k - 1).factorial : ℝ) := by positivity
  have hsep := heathBrownPairCountTwo_index_separation hmuPos hg hgd
    (fun x hx => heathBrownDerivativeCoordinate_last_lower hk (hkLower x hx))
    hp hspread
  calc
    |(m : ℝ) - n| ≤
        (4 * (((H : ℝ) ^ (k - 1))⁻¹)) /
          (lambda / ((k - 1).factorial : ℝ)) := hsep
    _ = 4 * ((k - 1).factorial : ℝ) /
        (lambda * (H : ℝ) ^ (k - 1)) := by
      field_simp

#print axioms deriv_heathBrownDerivativeCoordinate
#print axioms deriv_heathBrownDerivativeCoordinate_last
#print axioms heathBrownDerivativeCoordinate_last_lower
#print axioms heathBrownDerivativeCoordinate_last_upper
#print axioms heathBrownPairCountTwo_source_separation

end

end GafniTao
