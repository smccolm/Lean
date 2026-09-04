import GafniTao.HeathBrownHChoice

/-!
# The refined count at Heath-Brown's chosen scale

This specializes the finite count to the literal floor
`H = floor ((A * lambda)^(-1/k))`.  The hypothesis `8 <= H` is precisely the
large-block branch in which the two periodic tents have half-width at most
one half; the complementary bounded-`H` branch belongs to the final
exponential-sum assembly.
-/

namespace GafniTao

noncomputable section

theorem heathBrownPairCount_card_cast_le_at_chosen_scale
    {N k : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hcoordLow : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLowD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hcoordLast : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLastD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let H := heathBrownHChoice k A lambda
    let K := heathBrownBlockParameter A lambda N
    let D := heathBrownShiftBound N k H lambda
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((heathBrownPairCount N k H f).card : ℝ) ≤
      4 * K *
        (N + 2 * (((D : ℝ) + c) * (b + a * D) *
          (1 + Real.log N))) := by
  dsimp only
  have hwidth := heathBrown_width_le_half_of_eight_le hk hlargeH
  exact heathBrownPairCount_card_cast_le_refined_raw
    hk hN (heathBrownHChoice_pos (by omega) hA hlambda hsmall)
    hA.le hlambda hsmall hwidth.1 hwidth.2 hcoordLow hcoordLowD
    hcoordLast hcoordLastD hraw hrawd hkBounds

#print axioms heathBrownPairCount_card_cast_le_at_chosen_scale

end

end GafniTao
