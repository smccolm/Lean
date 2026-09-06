import GafniTao.HeathBrownActualSourceColorPhysicalCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# Removing the fixed dilations from the physical low-cell majorants

The actual Type-I/Type-II colour consumer leaves three literal physical
majorants: the direct Type-I term, the reflected Type-I term, and the
powered Type-II term. This file removes only their fixed dyadic dilations.
The reflected exponent `1 + 2*d` and every finite exponent loss remain
visible. Parameter optimization is deliberately postponed to a separate
finite theorem.
-/

open Filter

namespace GafniTao

noncomputable section

/-- The exact exponent left after removing fixed dilations from the two
Type-I physical majorants. -/
noncomputable def heathBrownTypeIEnvelopeExponent
    (d zetaExtract sigma0 zetaRel zetaCard zetaFixed : Real) : Real :=
  let e := heathBrownLowCellExponent sigma0 zetaRel zetaCard
  max (e + zetaFixed)
    (zetaExtract + reflectedPhysicalBeta d * e + zetaFixed)

/-- The exact exponent left after removing the fixed dilation from the
powered Type-II physical majorant. -/
noncomputable def heathBrownTypeIIEnvelopeExponent
    (sigma eta zetaShell zetaConst zetaDil zetaRel zetaCard delta2
      zetaFixed : Real) : Real :=
  let P := Nat.ceil (4 / delta2)
  let sigma0 := heathBrownEffectiveSigma sigma eta zetaShell zetaConst
    (P + 1) - zetaDil
  max (heathBrownLowFirstSlope sigma0)
      (heathBrownLowSecondSlope sigma0) +
    4 * (zetaRel + heathBrownCardinalityShift zetaCard) + zetaFixed

theorem eventually_heathBrownTypeIPhysicalMajorant_le
    {sigma d zetaExtract sigma0 zetaRel zetaCard zetaFixed : Real}
    {Pcap : Nat} (hzetaFixed : 0 < zetaFixed) :
    Filter.Eventually (fun U : Real =>
      heathBrownTypeIPhysicalMajorant sigma U d zetaExtract sigma0
          zetaRel zetaCard Pcap <=
        U ^ heathBrownTypeIEnvelopeExponent d zetaExtract sigma0
          zetaRel zetaCard zetaFixed) atTop := by
  let e := heathBrownLowCellExponent sigma0 zetaRel zetaCard
  let beta := reflectedPhysicalBeta d
  let g := (sigma - 1 / 2) / 2
  let Pref := reflectedPhysicalPowerCap d (2 / g)
  let Ddirect : Real := (2 : Real) ^ Pcap * 6
  let Dreflect : Real := (2 : Real) ^ Pref
  have hDirect := eventually_const_mul_rpow_le_rpow
    (D := Ddirect ^ e) (a := e) (b := e + zetaFixed) (by linarith)
  have hReflect := eventually_const_mul_rpow_le_rpow
    (D := Dreflect ^ e) (a := zetaExtract + beta * e)
      (b := zetaExtract + beta * e + zetaFixed) (by linarith)
  filter_upwards [hDirect, hReflect, eventually_ge_atTop (1 : Real)]
    with U hDirectU hReflectU hU
  have hU0 : 0 <= U := zero_le_one.trans hU
  have hDirectBase : (2 : Real) ^ Pcap * (6 * U) = Ddirect * U := by
    dsimp only [Ddirect]
    ring
  have hDirectTerm :
      (((2 : Real) ^ Pcap * (6 * U)) ^ e) <= U ^ (e + zetaFixed) := by
    rw [hDirectBase, Real.mul_rpow (by positivity : 0 <= Ddirect) hU0]
    exact hDirectU
  have hReflectTerm :
      U ^ zetaExtract * ((Dreflect * U ^ beta) ^ e) <=
        U ^ (zetaExtract + beta * e + zetaFixed) := by
    rw [Real.mul_rpow (by positivity : 0 <= Dreflect)
      (Real.rpow_nonneg hU0 beta), <- Real.rpow_mul hU0 beta e]
    calc
      U ^ zetaExtract * (Dreflect ^ e * U ^ (beta * e)) =
          Dreflect ^ e * U ^ (zetaExtract + beta * e) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hU)]
        ring
      _ <= U ^ (zetaExtract + beta * e + zetaFixed) := hReflectU
  dsimp only [heathBrownTypeIPhysicalMajorant, e, g, Pref, beta,
    heathBrownTypeIEnvelopeExponent]
  apply max_le
  · exact hDirectTerm.trans (Real.rpow_le_rpow_of_exponent_le hU
      (le_max_left _ _))
  · exact hReflectTerm.trans (Real.rpow_le_rpow_of_exponent_le hU
      (le_max_right _ _))

theorem eventually_heathBrownTypeIIPhysicalMajorant_le
    {sigma eta zetaShell zetaConst zetaDil zetaRel zetaCard delta2
        zetaFixed : Real}
    (hzetaFixed : 0 < zetaFixed) :
    Filter.Eventually (fun U : Real =>
      heathBrownTypeIIPhysicalMajorant sigma U eta zetaShell zetaConst
          zetaDil zetaRel zetaCard delta2 <=
        U ^ heathBrownTypeIIEnvelopeExponent sigma eta zetaShell zetaConst
          zetaDil zetaRel zetaCard delta2 zetaFixed) atTop := by
  let P := Nat.ceil (4 / delta2)
  let sigma0 := heathBrownEffectiveSigma sigma eta zetaShell zetaConst
    (P + 1) - zetaDil
  let e := max (heathBrownLowFirstSlope sigma0)
      (heathBrownLowSecondSlope sigma0) +
    4 * (zetaRel + heathBrownCardinalityShift zetaCard)
  let D : Real := (2 : Real) ^ P
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := D ^ e) (a := e) (b := e + zetaFixed) (by linarith)
  filter_upwards [hAbsorb, eventually_ge_atTop (1 : Real)]
    with U hAbsorbU hU
  have hU0 : 0 <= U := zero_le_one.trans hU
  dsimp only [heathBrownTypeIIPhysicalMajorant,
    heathBrownTypeIIEnvelopeExponent, P, sigma0, e]
  rw [Real.mul_rpow (by positivity : 0 <= D) hU0]
  simpa only [D] using hAbsorbU

/-- The exact maximum of the actual Type-I and Type-II physical majorants,
with no parameter optimization hidden in the statement. -/
theorem eventually_heathBrown_physical_majorants_le
    {sigma d zetaExtract sigma0 zetaRel zetaCard zetaFixed eta zetaShell
        zetaConst zetaDil delta2 : Real}
    {Pcap : Nat} (hzetaFixed : 0 < zetaFixed) :
    Filter.Eventually (fun U : Real =>
      max (heathBrownTypeIPhysicalMajorant sigma U d zetaExtract sigma0
            zetaRel zetaCard Pcap)
          (heathBrownTypeIIPhysicalMajorant sigma U eta zetaShell zetaConst
            zetaDil zetaRel zetaCard delta2) <=
        U ^ max
          (heathBrownTypeIEnvelopeExponent d zetaExtract sigma0 zetaRel
            zetaCard zetaFixed)
          (heathBrownTypeIIEnvelopeExponent sigma eta zetaShell zetaConst
            zetaDil zetaRel zetaCard delta2 zetaFixed)) atTop := by
  have hI := eventually_heathBrownTypeIPhysicalMajorant_le
    (sigma := sigma) (d := d) (zetaExtract := zetaExtract)
    (sigma0 := sigma0) (zetaRel := zetaRel) (zetaCard := zetaCard)
    (Pcap := Pcap) hzetaFixed
  have hII := eventually_heathBrownTypeIIPhysicalMajorant_le
    (sigma := sigma) (eta := eta) (zetaShell := zetaShell)
    (zetaConst := zetaConst) (zetaDil := zetaDil) (zetaRel := zetaRel)
    (zetaCard := zetaCard) (delta2 := delta2) hzetaFixed
  filter_upwards [hI, hII, eventually_ge_atTop (1 : Real)]
    with U hIU hIIU hU
  apply max_le
  · exact hIU.trans (Real.rpow_le_rpow_of_exponent_le hU
      (le_max_left _ _))
  · exact hIIU.trans (Real.rpow_le_rpow_of_exponent_le hU
      (le_max_right _ _))

#print axioms eventually_heathBrownTypeIPhysicalMajorant_le
#print axioms eventually_heathBrownTypeIIPhysicalMajorant_le
#print axioms eventually_heathBrown_physical_majorants_le

end

end GafniTao
