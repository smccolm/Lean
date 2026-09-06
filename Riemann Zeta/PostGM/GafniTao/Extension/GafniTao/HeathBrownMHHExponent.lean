import GafniTao.HeathBrownActualMHHCardinality
import GafniTao.HeathBrownCardinalityExponent

/-!
# Logarithmic exponent form of the high-line MHH estimate

The sixth-power member of Montgomery--Halász--Huxley gives the source cap
`rho <= max (2-2*sigma) (tau+4-6*sigma)` after explicit coefficient and
epsilon losses.  Nothing asymptotic is hidden in this conversion.
-/

namespace GafniTao

noncomputable section

/-- A threshold `V >= x^sigma` controls the sixth-power MHH quotient. -/
theorem quotient_four_six_le_rpow_sub
    {x V sigma : Real} (hx : 0 < x) (hV : x ^ sigma ≤ V) :
    x ^ 4 / V ^ 6 ≤ x ^ (4 - 6 * sigma) := by
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hx sigma
  have hVPos : 0 < V := hxSigmaPos.trans_le hV
  have hSix : (x ^ sigma) ^ 6 ≤ V ^ 6 :=
    pow_le_pow_left₀ hxSigmaPos.le hV 6
  have hDiv : x ^ 4 / V ^ 6 ≤ x ^ 4 / (x ^ sigma) ^ 6 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hxSigmaPos 6) hSix
  have hNum : x ^ 4 = x ^ (4 : Real) := (Real.rpow_natCast x 4).symm
  have hDen : (x ^ sigma) ^ 6 = x ^ (sigma * 6) := by
    calc
      (x ^ sigma) ^ 6 = (x ^ sigma) ^ (6 : Real) :=
        (Real.rpow_natCast (x ^ sigma) 6).symm
      _ = x ^ (sigma * 6) := (Real.rpow_mul hx.le sigma 6).symm
  calc
    x ^ 4 / V ^ 6 ≤ x ^ 4 / (x ^ sigma) ^ 6 := hDiv
    _ = x ^ (4 - 6 * sigma) := by
      rw [hNum, hDen, ← Real.rpow_sub hx]
      congr 1
      ring_nf

/-- Exact logarithmic consequence of the common-length high-line MHH
majorant.  The output displays separately the MHH epsilon loss and the fixed
coefficient loss. -/
theorem heathBrown_mhh_card_log_le
    {x B V card C sigma tau epsilonMHH zeta : Real}
    (hx : 1 < x) (hB : 0 < B) (hcard : 0 < card)
    (hC : 0 ≤ C)
    (hThreshold : x ^ sigma ≤ V)
    (hBExact : x ^ tau = B)
    (hCardBound : card ≤ C * B ^ epsilonMHH *
      (x ^ 2 / V ^ 2 + B * x ^ 4 / V ^ 6))
    (hCoeff : 2 * C ≤ x ^ zeta) :
    heathBrownLogExponent x card ≤
      zeta + epsilonMHH * tau +
        max (2 - 2 * sigma) (tau + 4 - 6 * sigma) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : 1 ≤ x := hx.le
  have hquad := quotient_sq_le_rpow_sub hx0 hThreshold
  have hsix := quotient_four_six_le_rpow_sub hx0 hThreshold
  have hheight : B * x ^ 4 / V ^ 6 ≤
      x ^ (tau + 4 - 6 * sigma) := by
    calc
      B * x ^ 4 / V ^ 6 = B * (x ^ 4 / V ^ 6) := by ring_nf
      _ ≤ B * x ^ (4 - 6 * sigma) := by gcongr
      _ = x ^ tau * x ^ (4 - 6 * sigma) := by rw [hBExact]
      _ = x ^ (tau + 4 - 6 * sigma) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring_nf
  let q := max (2 - 2 * sigma) (tau + 4 - 6 * sigma)
  have hsum : x ^ 2 / V ^ 2 + B * x ^ 4 / V ^ 6 ≤
      2 * x ^ q := by
    calc
      x ^ 2 / V ^ 2 + B * x ^ 4 / V ^ 6 ≤
          x ^ (2 - 2 * sigma) + x ^ (tau + 4 - 6 * sigma) :=
        add_le_add hquad hheight
      _ ≤ 2 * x ^ q := add_two_rpow_le_two_mul_max hx1
  have hBEpsilon : B ^ epsilonMHH = x ^ (epsilonMHH * tau) := by
    rw [← hBExact]
    calc
      (x ^ tau) ^ epsilonMHH = x ^ (tau * epsilonMHH) :=
        (Real.rpow_mul hx0.le tau epsilonMHH).symm
      _ = x ^ (epsilonMHH * tau) := by ring_nf
  have hPower : card ≤ x ^
      (zeta + epsilonMHH * tau + q) := by
    calc
      card ≤ C * B ^ epsilonMHH *
          (x ^ 2 / V ^ 2 + B * x ^ 4 / V ^ 6) := hCardBound
      _ ≤ C * B ^ epsilonMHH * (2 * x ^ q) := by
        gcongr
      _ = (2 * C) * B ^ epsilonMHH * x ^ q := by ring_nf
      _ ≤ x ^ zeta * B ^ epsilonMHH * x ^ q := by
        gcongr
      _ = x ^ zeta * x ^ (epsilonMHH * tau) * x ^ q := by
        rw [hBEpsilon]
      _ = x ^ (zeta + epsilonMHH * tau + q) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
  have hExact : x ^ heathBrownLogExponent x card = card :=
    rpow_heathBrownLogExponent hx hcard
  apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
  simpa only [hExact] using hPower

#print axioms quotient_four_six_le_rpow_sub
#print axioms heathBrown_mhh_card_log_le

end

end GafniTao
