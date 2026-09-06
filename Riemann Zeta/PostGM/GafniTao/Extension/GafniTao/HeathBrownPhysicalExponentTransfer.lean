import GafniTao.HeathBrownLogarithmicRelation
import GafniTao.HeathBrownFiniteLossAbsorption

/-!
# Returning Heath--Brown logarithmic bounds to the physical scale

The finite Heath--Brown packets define every exponent from the quantity it
measures.  This file records the exact converse step: an affine inequality
between those logarithmic exponents gives a power bound for the original
energy.  No asymptotic notation or independently chosen exponent occurs in
this conversion.
-/

namespace GafniTao

noncomputable section

/-- If `E = x^rhoStar` and `B = x^tau`, an affine logarithmic estimate for
`rhoStar` gives the corresponding exact power estimate at base `x`. -/
theorem rpow_le_rpow_of_heathBrownLogExponent_le
    {x E B rhoStar tau slope loss : Real}
    (hx : 1 < x) (hE : 0 < E) (hB : 0 < B)
    (hrho : heathBrownLogExponent x E = rhoStar)
    (htau : heathBrownLogExponent x B = tau)
    (hbound : rhoStar <= slope * tau + loss) :
    E <= B ^ slope * x ^ loss := by
  have hx0 : 0 <= x := (zero_lt_one.trans hx).le
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hmono := (Real.strictMono_rpow_of_base_gt_one hx).monotone hbound
  rw [<- hrho, rpow_heathBrownLogExponent hx hE,
    <- htau, Real.rpow_add hxpos,
    show slope * heathBrownLogExponent x B =
        heathBrownLogExponent x B * slope by ring,
    Real.rpow_mul hx0,
    rpow_heathBrownLogExponent hx hB] at hmono
  exact hmono

/-- If the logarithmic base is at most the physical ambient height, a
nonnegative loss exponent can be moved from that base to the ambient height.
This is the exact finite inequality used before absorbing fixed dyadic
factors. -/
theorem physical_rpow_bound_of_heathBrownLogExponent_le
    {x E B rhoStar tau slope loss : Real}
    (hx : 1 < x) (hE : 0 < E) (hB : 0 < B)
    (hxB : x <= B) (hloss : 0 <= loss)
    (hrho : heathBrownLogExponent x E = rhoStar)
    (htau : heathBrownLogExponent x B = tau)
    (hbound : rhoStar <= slope * tau + loss) :
    E <= B ^ slope * B ^ loss := by
  calc
    E <= B ^ slope * x ^ loss :=
      rpow_le_rpow_of_heathBrownLogExponent_le hx hE hB hrho htau hbound
    _ <= B ^ slope * B ^ loss := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_lt_one.trans hx).le hxB hloss)
        (Real.rpow_nonneg hB.le slope)

/-- Multiplicative powers on a positive physical base recombine into the
sum of their exponents. -/
theorem physical_rpow_bound_recombine
    {E B slope loss : Real} (hB : 0 < B)
    (hE : E <= B ^ slope * B ^ loss) :
    E <= B ^ (slope + loss) := by
  simpa only [Real.rpow_add hB] using hE

/-- An affine exponent bound in a finite logarithmic packet gives the
recombined physical power bound. -/
theorem heathBrown_physical_of_packet_bound
    {x E B rhoStar tau slope loss : Real}
    (hx : 1 < x) (hE : 0 < E) (hB : 0 < B) (hxB : x <= B)
    (hloss : 0 <= loss)
    (hrho : heathBrownLogExponent x E = rhoStar)
    (htau : heathBrownLogExponent x B = tau)
    (hbound : rhoStar <= slope * tau + loss) :
    E <= B ^ (slope + loss) :=
  physical_rpow_bound_recombine hB
    (physical_rpow_bound_of_heathBrownLogExponent_le
      hx hE hB hxB hloss hrho htau hbound)

/-- A fixed dilation of the physical height costs an arbitrarily small strict
power.  This is the exact asymptotic step used to remove the common factor
`2^P` after `P` has been fixed by the epsilon budget. -/
theorem eventually_fixed_dilation_rpow_le_rpow
    {D q zeta : Real} (hD : 0 <= D) (hzeta : 0 < zeta) :
    Filter.Eventually (fun U : Real =>
      (D * U) ^ q <= U ^ (q + zeta)) Filter.atTop := by
  have hSmall := eventually_const_mul_rpow_le_rpow
    (D := D ^ q) (a := q) (b := q + zeta) (by linarith)
  filter_upwards [hSmall, Filter.eventually_ge_atTop (0 : Real)]
    with U hSmallU hU
  rw [Real.mul_rpow hD hU]
  exact hSmallU

#print axioms rpow_le_rpow_of_heathBrownLogExponent_le
#print axioms physical_rpow_bound_of_heathBrownLogExponent_le
#print axioms physical_rpow_bound_recombine
#print axioms heathBrown_physical_of_packet_bound
#print axioms eventually_fixed_dilation_rpow_le_rpow

end

end GafniTao
