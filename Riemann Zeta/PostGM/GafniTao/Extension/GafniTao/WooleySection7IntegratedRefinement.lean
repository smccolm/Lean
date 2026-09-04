import GafniTao.WooleySection7LocalBound

/-!
# Integrating Wooley's equation (7.22)

This file applies the literal residue-refinement inequality (7.22) inside
the finite Fourier average defining the mixed moment.  It is the analytic
substitution used between equations (7.21) and (7.23); no bounded surrogate
for either normalized exponential sum is introduced.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Equation (7.22) integrated against the unchanged right-hand factor in
the mixed moment. -/
theorem wooley_equation_7_22_integrated_native
    {k p r a b nu gammaVal B s : ℕ} [NeZero p] [NeZero (p ^ B)]
    (hr : 1 ≤ r)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (kappa : ZMod (p ^ (a + wooleySection7HPrime k r a b gammaVal)))
    (eta : ZMod (p ^ b)) :
    wooleySourceResidueMassSq gamma
          (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
        wooleySourcePolynomialMixedResidueMoment phi s r p B
          (a + wooleySection7HPrime k r a b gammaVal) b gamma kappa eta ≤
      (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
          wooleyTriangular r *
        ∑ xiPrime ∈ wooleyResidueRefinementFiber p
            (a + wooleySection7HPrime k r a b gammaVal)
            (wooleySection7NextB k r b)
            (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
          wooleySourceResidueMassSq gamma
              (p ^ wooleySection7NextB k r b) xiPrime *
            wooleySourcePolynomialMixedResidueMoment phi s r p B
              (wooleySection7NextB k r b) b gamma xiPrime eta := by
  let A := a + wooleySection7HPrime k r a b gammaVal
  let bPrime := wooleySection7NextB k r b
  let hAb : A ≤ bPrime :=
    wooley_section7_a_add_HPrime_le_nextB hr hBPrime
  let factor : ℝ := (p ^ (bPrime - A) : ℝ) ^ wooleyTriangular r
  let mass : ℝ := wooleySourceResidueMassSq gamma (p ^ A) kappa
  let scale : ℝ := ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹
  let rightNorm : (Fin k → ZMod (p ^ B)) → ℝ := fun alpha =>
    ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
      (2 * (s - wooleyTriangular r))
  have hpointwise : ∀ alpha : Fin k → ZMod (p ^ B),
      mass *
          (‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
            (2 * wooleyTriangular r) * rightNorm alpha) ≤
        factor *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p A bPrime hAb kappa,
            wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
              (‖wooleySourceNormalizedPolynomialResidueSum
                  phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) *
                rightNorm alpha) := by
    intro alpha
    have hrefine := wooley_equation_7_22_native
      (k := k) (p := p) (r := r) (a := a) (b := b) (nu := nu)
      (gammaVal := gammaVal) (B := B) hr hBPrime phi gamma alpha kappa
    have hright : 0 ≤
        ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
          (2 * (s - wooleyTriangular r)) :=
      pow_nonneg (norm_nonneg _) _
    have hmul := mul_le_mul_of_nonneg_right hrefine hright
    dsimp only [A, bPrime, hAb, factor, mass, rightNorm]
    calc
      wooleySourceResidueMassSq gamma
            (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
          (‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
              (2 * wooleyTriangular r) *
            ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
              (2 * (s - wooleyTriangular r))) =
        (wooleySourceResidueMassSq gamma
              (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
            ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
              (2 * wooleyTriangular r)) *
          ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
            (2 * (s - wooleyTriangular r)) := by ring
      _ ≤ ((p ^ (wooleySection7NextB k r b -
              (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
              wooleyTriangular r *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + wooleySection7HPrime k r a b gammaVal)
                (wooleySection7NextB k r b)
                (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
              wooleySourceResidueMassSq gamma
                  (p ^ wooleySection7NextB k r b) xiPrime *
                ‖wooleySourceNormalizedPolynomialResidueSum
                    phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r)) *
          ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
            (2 * (s - wooleyTriangular r)) := hmul
      _ = (p ^ (wooleySection7NextB k r b -
              (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
              wooleyTriangular r *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + wooleySection7HPrime k r a b gammaVal)
                (wooleySection7NextB k r b)
                (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
              wooleySourceResidueMassSq gamma
                  (p ^ wooleySection7NextB k r b) xiPrime *
                (‖wooleySourceNormalizedPolynomialResidueSum
                    phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) *
                  ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
                    (2 * (s - wooleyTriangular r))) := by
        rw [mul_assoc, sum_mul]
        apply congrArg (fun x : ℝ =>
          (p ^ (wooleySection7NextB k r b -
            (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
              wooleyTriangular r * x)
        apply Finset.sum_congr rfl
        intro xiPrime hxiPrime
        ring
  unfold wooleySourcePolynomialMixedResidueMoment
  have hsum :
      (∑ alpha : Fin k → ZMod (p ^ B),
        mass *
          (‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
              (2 * wooleyTriangular r) * rightNorm alpha)) ≤
        ∑ alpha : Fin k → ZMod (p ^ B),
          factor *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p A bPrime hAb kappa,
              wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                (‖wooleySourceNormalizedPolynomialResidueSum
                    phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) *
                  rightNorm alpha) := by
    apply Finset.sum_le_sum
    intro alpha halpha
    exact hpointwise alpha
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  dsimp only [scale, mass, factor, A, bPrime, hAb, rightNorm] at hscaled ⊢
  calc
    wooleySourceResidueMassSq gamma
          (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
        (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
          ∑ alpha : Fin k → ZMod (p ^ B),
            ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
                (2 * wooleyTriangular r) *
              ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
                (2 * (s - wooleyTriangular r))) =
      (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod (p ^ B),
          wooleySourceResidueMassSq gamma
              (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
            (‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha kappa‖ ^
                (2 * wooleyTriangular r) *
              ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
                (2 * (s - wooleyTriangular r))) := by
        rw [← mul_sum]
        ring
    _ ≤ (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod (p ^ B),
          (p ^ (wooleySection7NextB k r b -
              (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
              wooleyTriangular r *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + wooleySection7HPrime k r a b gammaVal)
                (wooleySection7NextB k r b)
                (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
              wooleySourceResidueMassSq gamma
                  (p ^ wooleySection7NextB k r b) xiPrime *
                (‖wooleySourceNormalizedPolynomialResidueSum
                    phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) *
                  ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
                    (2 * (s - wooleyTriangular r))) := hscaled
    _ = (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
          wooleyTriangular r *
        ∑ xiPrime ∈ wooleyResidueRefinementFiber p
            (a + wooleySection7HPrime k r a b gammaVal)
            (wooleySection7NextB k r b)
            (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
          wooleySourceResidueMassSq gamma
              (p ^ wooleySection7NextB k r b) xiPrime *
            (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              ∑ alpha : Fin k → ZMod (p ^ B),
                ‖wooleySourceNormalizedPolynomialResidueSum
                    phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) *
                  ‖wooleySourceNormalizedPolynomialResidueSum phi gamma alpha eta‖ ^
                    (2 * (s - wooleyTriangular r))) := by
      simp only [mul_sum]
      ring_nf
      rw [Finset.sum_comm]

#print axioms wooley_equation_7_22_integrated_native

end

end GafniTao
