import GafniTao.HeathBrownLongSourceThreshold

/-!
# Exact-power threshold transfer for actual Type-I colours

The common-cap estimate is deliberately too crude for a Type-I colour: it
replaces the source power `p` by a cap of order `1 / delta2` before the
physical detector loss is converted to the polynomial scale.  This file
keeps the literal `p` through that conversion.  The factor `p` then cancels
against the lower source scale, leaving a loss proportional to
`(delta2 + zeta) / delta1`, as in the source zero-density-energy argument.
-/

open Filter

namespace GafniTao

noncomputable section

/-- Exact version of the powered threshold lower bound, retaining the
selected source power rather than replacing it by a uniform cap. -/
theorem heathBrownPoweredThreshold_lower_of_source_exact_power
    {U sigma eta zetaShell zetaConst Cp L : Real} {N p : Nat}
    (hU : 1 <= U) (hN : 0 < N) (hp : 0 < p)
    (heta : 0 < eta) (hzetaShell : 0 <= zetaShell)
    (hCp : 0 < Cp)
    (hSource : U ^ (-zetaShell) *
        (N : Real) ^ (sigma - eta) <= L)
    (hDenom : Cp * (p : Real) *
        (2 : Real) ^ ((p : Real) * eta) <= U ^ zetaConst) :
    U ^ (-(zetaShell * (p : Real) + zetaConst)) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) <=
      heathBrownPoweredThreshold N p L Cp eta := by
  simpa using heathBrownPoweredThreshold_lower_of_source
    (P := p) hU hN hp (le_refl p) heta hzetaShell hCp hSource hDenom

/-- A lower physical scale converts an exact powered height loss into a
loss on the powered polynomial base.  The displayed bound is intentionally
slightly weaker in the constant loss, using only `1 <= p`; this keeps the
result uniform in the selected power without reintroducing a power cap. -/
theorem rpow_power_scale_loss_le_of_height_lower
    {U N alpha zetaShell zetaConst : Real} {p : Nat}
    (hU : 1 <= U) (hN : 0 < N) (hp : 0 < p)
    (halpha : 0 < alpha) (hzetaShell : 0 <= zetaShell)
    (hzetaConst : 0 <= zetaConst)
    (hLower : U ^ alpha <= N) :
    (N ^ p) ^ (-(zetaShell + zetaConst) / alpha) <=
      U ^ (-(zetaShell * (p : Real) + zetaConst)) := by
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hNPos : 0 < N := hN
  have hpR : (1 : Real) <= p := by exact_mod_cast hp
  have hBase : U ^ (alpha * (p : Real)) <= N ^ p := by
    calc
      U ^ (alpha * (p : Real)) = (U ^ alpha) ^ (p : Nat) := by
        rw [<- Real.rpow_natCast, <- Real.rpow_mul hUPos.le]
      _ <= N ^ (p : Nat) := pow_le_pow_left₀
        (Real.rpow_nonneg hUPos.le alpha) hLower p
      _ = N ^ p := rfl
  have hLoss : 0 <= (zetaShell + zetaConst) / alpha := by positivity
  have hNegative := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hUPos _) hBase
    (neg_nonpos.mpr hLoss)
  have hExponent :
      -(alpha * (p : Real)) * ((zetaShell + zetaConst) / alpha) <=
        -(zetaShell * (p : Real) + zetaConst) := by
    field_simp [halpha.ne']
    nlinarith
  calc
    (N ^ p) ^ (-(zetaShell + zetaConst) / alpha) <=
        (U ^ (alpha * (p : Real))) ^
          (-(zetaShell + zetaConst) / alpha) := by
      simpa only [neg_div] using hNegative
    _ = U ^ ((alpha * (p : Real)) *
          (-(zetaShell + zetaConst) / alpha)) :=
      (Real.rpow_mul hUPos.le _ _).symm
    _ = U ^ (-(alpha * (p : Real)) *
          ((zetaShell + zetaConst) / alpha)) := by
      congr 1
      ring
    _ <= U ^ (-(zetaShell * (p : Real) + zetaConst)) :=
      Real.rpow_le_rpow_of_exponent_le hU hExponent

/-- Exact Type-I powered threshold expressed on the actual powered source
scale.  No factor involving a uniform cap multiplies `zetaShell`. -/
theorem heathBrownTypeIPoweredThreshold_lower_on_power_scale
    {U sigma eta zetaShell zetaConst Cp L alpha : Real} {N p : Nat}
    (hU : 1 <= U) (hN : 0 < N) (hp : 0 < p)
    (heta : 0 < eta) (halpha : 0 < alpha)
    (hzetaShell : 0 <= zetaShell) (hzetaConst : 0 <= zetaConst)
    (hCp : 0 < Cp)
    (hSource : U ^ (-zetaShell) *
        (N : Real) ^ (sigma - eta) <= L)
    (hDenom : Cp * (p : Real) *
        (2 : Real) ^ ((p : Real) * eta) <= U ^ zetaConst)
    (hLower : U ^ alpha <= (N : Real)) :
    ((N ^ p : Nat) : Real) ^
        (sigma - 2 * eta - (zetaShell + zetaConst) / alpha) <=
      heathBrownPoweredThreshold N p L Cp eta := by
  have hMPos : (0 : Real) < (N ^ p : Nat) := by positivity
  have hHeight := rpow_power_scale_loss_le_of_height_lower
    hU (show (0 : Real) < N by exact_mod_cast hN) hp halpha
      hzetaShell hzetaConst hLower
  have hExact := heathBrownPoweredThreshold_lower_of_source_exact_power
    hU hN hp heta hzetaShell hCp hSource hDenom
  calc
    ((N ^ p : Nat) : Real) ^
        (sigma - 2 * eta - (zetaShell + zetaConst) / alpha) =
      ((N ^ p : Nat) : Real) ^
          (-(zetaShell + zetaConst) / alpha) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by
      rw [<- Real.rpow_add hMPos]
      congr 1
      ring
    _ <= U ^ (-(zetaShell * (p : Real) + zetaConst)) *
        ((N ^ p : Nat) : Real) ^ (sigma - 2 * eta) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hMPos.le _)
      simpa only [Nat.cast_pow] using hHeight
    _ <= heathBrownPoweredThreshold N p L Cp eta := hExact

#print axioms heathBrownPoweredThreshold_lower_of_source_exact_power
#print axioms rpow_power_scale_loss_le_of_height_lower
#print axioms heathBrownTypeIPoweredThreshold_lower_on_power_scale

end

end GafniTao
