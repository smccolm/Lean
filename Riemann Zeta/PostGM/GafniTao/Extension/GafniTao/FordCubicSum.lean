import GafniTao.FordUnimodalSum

/-!
# Ford's dyadic cubic sum

This file applies the exact unimodal sum-to-integral lemma to the literal
cubic exponent arising from Ford's dyadic decomposition.  It is the first
source-specific step in the proof of Ford's Lemma 7.3.
-/

namespace GafniTao

noncomputable section

theorem fordCubicExpSum_le_peak_add_integral
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (r : ℕ) :
    (∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j)) ≤
      Real.exp (fordCubicExponent D sigma t
        (fordCubicTurningPoint D sigma t)) +
        ∫ x in (0 : ℝ)..r,
          Real.exp (fordCubicExponent D sigma t x) := by
  have h := sum_range_le_peak_add_integral_of_unimodal
    (f := fun x => Real.exp (fordCubicExponent D sigma t x))
    (c := fordCubicTurningPoint D sigma t)
    (fordCubicTurningPoint_nonneg D sigma t)
    (by
      unfold fordCubicExponent fordCubicA fordCubicB
      fun_prop)
    (fun x => (Real.exp_pos _).le)
    (fordCubicExp_monotoneOn_left hsigma hD ht)
    (fordCubicExp_antitoneOn_right hsigma hD ht)
    r
  simpa only [fordDyadicExponent_eq_cubic] using h

#print axioms fordCubicExpSum_le_peak_add_integral

end

end GafniTao
