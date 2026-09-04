import GafniTao.HeathBrownCountLocalization
import GafniTao.HeathBrownDerivativeCoordinates

/-!
# The last-coordinate half-unit bound

For Heath-Brown's exact block parameter, the normalized `(k-1)`-st
derivative varies by at most one half across every localized pair.  This is
the step that turns the nearest-integer condition into an ordinary absolute
value condition.
-/

namespace GafniTao

noncomputable section

theorem heathBrown_actualBlock_last_coordinate_spread
    {N k H m n : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H
      (heathBrownBlockParameter A lambda N) f) :
    |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤ 1 / 2 := by
  let F : ℝ → ℝ := fun x => heathBrownDerivativeCoordinate f (k - 1) x
  let M : ℝ := A * lambda / ((k - 1).factorial : ℝ)
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      0 ≤ deriv F x := by
    intro x hx
    dsimp [F]
    have h := heathBrownDerivativeCoordinate_last_lower hk (hkBounds x hx).1
    exact le_trans (by positivity : 0 ≤ lambda / ((k - 1).factorial : ℝ)) h
  have hderivUpper : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      deriv F x ≤ M := by
    intro x hx
    exact heathBrownDerivativeCoordinate_last_upper hk (hkBounds x hx).2
  have hindex := heathBrown_pairCountTwo_index_le_block_length hp
  have hvariation := heathBrown_abs_difference_le_deriv_bound
    (g := F) (M := M) hg hgd hderivLower hderivUpper
    (m := m) (n := n)
    (by exact (mem_heathBrownPairCountTwo.mp hp).2.1)
    (by exact (mem_heathBrownPairCountTwo.mp hp).2.2.2.1)
  have hfact : (1 : ℝ) ≤ ((k - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  have hMle : M ≤ A * lambda := by
    dsimp [M]
    exact div_le_self (mul_nonneg hA hlambda.le) hfact
  have hscale := heathBrown_block_scale_le_half
    (A := A) (lambda := lambda) (N := N) hsmall
  have hlengthNonneg :
      0 ≤ 1 + (N : ℝ) / heathBrownBlockParameter A lambda N := by positivity
  calc
    |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤
        M * |(m : ℝ) - n| := hvariation
    _ ≤ M * (1 + (N : ℝ) / heathBrownBlockParameter A lambda N) :=
      mul_le_mul_of_nonneg_left hindex hMnonneg
    _ ≤ A * lambda *
        (1 + (N : ℝ) / heathBrownBlockParameter A lambda N) :=
      mul_le_mul_of_nonneg_right hMle hlengthNonneg
    _ ≤ 1 / 2 := hscale

theorem heathBrown_actualBlock_pair_source_separation
    {N k H m n : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H
      (heathBrownBlockParameter A lambda N) f) :
    |(m : ℝ) - n| ≤
      4 * ((k - 1).factorial : ℝ) /
        (lambda * (H : ℝ) ^ (k - 1)) := by
  apply heathBrownPairCountTwo_source_separation hk hlambda hg hgd
    (fun x hx => (hkBounds x hx).1) hp
  exact heathBrown_actualBlock_last_coordinate_spread
    hk hA hlambda hsmall hg hgd hkBounds hp

#print axioms heathBrown_actualBlock_last_coordinate_spread
#print axioms heathBrown_actualBlock_pair_source_separation

end

end GafniTao
