import GafniTao.HeathBrownHarmonicBound

/-!
# Assembly of Heath-Brown's refined finite count

This is the first theorem in the development that composes the literal
`mathcal N -> mathcal N_1 -> mathcal N_2` chain with the positive-shift
spacing estimate.  The result deliberately retains the exact natural block
parameter and shift cutoff; their source-scale simplification is performed in
the next layer.
-/

namespace GafniTao

noncomputable section

theorem heathBrownPairCount_card_cast_le_refined_raw
    {N k H : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hH : 0 < H)
    (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hwidth₁ : 4 * (((H : ℝ) ^ (k - 2))⁻¹) ≤ 1 / 2)
    (hwidth₂ : 4 * (((H : ℝ) ^ (k - 1))⁻¹) ≤ 1 / 2)
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
  let K := heathBrownBlockParameter A lambda N
  let D := heathBrownShiftBound N k H lambda
  let c : ℝ := 8 * ((k - 2).factorial : ℝ) *
    (((H : ℝ) ^ (k - 2))⁻¹) / lambda
  let b : ℝ := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
  let a : ℝ := A * lambda * N / ((k - 2).factorial : ℝ)
  have hpair : ((heathBrownPairCount N k H f).card : ℝ) ≤
      (heathBrownPairCountOne N k H f).card := by
    exact_mod_cast heathBrownPairCount_card_le_pairCountOne_card
      (N := N) (H := H) (f := f) hk
  have hlocal :=
    heathBrownPairCountOne_card_le_four_mul_block_mul_pairCountTwo
      (N := N) (k := k) (H := H) (K := K) (f := f)
      hH (heathBrownBlockParameter_pos A lambda N) hwidth₁ hwidth₂
  have htwo := heathBrownPairCountTwo_card_cast_le_harmonic
    (N := N) (k := k) (H := H) (f := f) (A := A) (lambda := lambda)
    hk hA hlambda hsmall hcoordLow hcoordLowD hcoordLast hcoordLastD
    hraw hrawd hkBounds
  dsimp only at htwo
  have hharm : (harmonic D : ℝ) ≤ 1 + Real.log N := by
    simpa only [D] using
      (heathBrownShiftBound_harmonic_le
        (k := k) (H := H) (lambda := lambda) hN)
  have hfactor : 0 ≤ ((D : ℝ) + c) * (b + a * D) := by
    dsimp only [a, b, c]
    positivity
  have hreplace :
      ((D : ℝ) + c) * (b + a * D) * (harmonic D : ℝ) ≤
        ((D : ℝ) + c) * (b + a * D) * (1 + Real.log N) :=
    mul_le_mul_of_nonneg_left hharm hfactor
  have htwo' :
      ((heathBrownPairCountTwo N k H K f).card : ℝ) ≤
        N + 2 * (((D : ℝ) + c) * (b + a * D) *
          (1 + Real.log N)) := by
    calc
      ((heathBrownPairCountTwo N k H K f).card : ℝ) ≤
          N + 2 * (((D : ℝ) + c) * (b + a * D) *
            (harmonic D : ℝ)) := by simpa only [K, D, c, b, a] using htwo
      _ ≤ N + 2 * (((D : ℝ) + c) * (b + a * D) *
          (1 + Real.log N)) := by gcongr
  exact hpair.trans (hlocal.trans
    (mul_le_mul_of_nonneg_left htwo' (by positivity)))

#print axioms heathBrownPairCount_card_cast_le_refined_raw

end

end GafniTao
