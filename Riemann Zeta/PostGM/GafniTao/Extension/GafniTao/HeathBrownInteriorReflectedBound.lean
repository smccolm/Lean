import GafniTao.HeathBrownInteriorReflectedEnergy
import GafniTao.HeathBrownReflectedPhysicalCell
import GafniTao.ReflectedExtractionLoss

/-!
# Reassembled physical energy bound for an interior Type-I reflection

This module applies the physical Heath--Brown estimate to every one of the
sixteen sign/dyadic cells produced by the actual frozen Poisson reflection,
then reassembles them.  The finite extraction loss remains an explicit small
power of the original height.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The actual reflected family, rather than a separately supplied family,
satisfies the reassembled physical low-cell energy estimate. -/
theorem eventually_interior_source_family_reflected_physical_bound
    {sigma d u epsilon eta zetaShell zetaReflect zetaPower zetaDil loss
        zetaRel zetaCard sigma0 v zetaExtract : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hd : 0 < d) (hdGap : d <= (sigma - 1 / 2) / 1000)
    (hu : 0 <= u) (huD : u <= d)
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaReflect : 0 < zetaReflect)
    (hzetaPower : 0 < zetaPower) (hzetaDil : 0 < zetaDil)
    (hloss : 0 < loss) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Upper : sigma0 <= 3 / 4)
    (hv : 0 < v) (hzetaExtract : 4 * v + 5 * d < zetaExtract)
    (hBudget :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      let beta := reflectedPhysicalBeta d
      u + d * (2 * sigma + 1) + beta * zetaShell + zetaReflect <=
        (loss + eta) / Uscale)
    (hEffective :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      sigma0 <= reflectedPhysicalEffectiveSigma sigma loss eta zetaShell
        zetaPower zetaDil d Uscale) :
    let g := (sigma - 1 / 2) / 2
    let Uscale := 2 / g
    let beta := reflectedPhysicalBeta d
    let Pcap := reflectedPhysicalPowerCap d Uscale
    let e := max (heathBrownLowFirstSlope sigma0)
        (heathBrownLowSecondSlope sigma0) +
      4 * (zetaRel + heathBrownCardinalityShift zetaCard)
    ∀ᶠ T : Real in atTop,
      forall {tau : Real} {Y A r : Nat} (W : Finset Real),
        A = Nat.floor (sharpZetaCutoff T) -> 0 < Y -> 2 <= r ->
        2 * (2 ^ r * Y) <= A ->
        tau = typeILogarithmicScale T (2 ^ r * Y) ->
        1 < tau -> tau < 2 -> W.Nonempty -> IsSeparated 1 W ->
        (forall t, t ∈ W -> T - T ^ d <= t ∧ t <= 2 * T + T ^ d) ->
        (forall t, t ∈ W ->
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : Nat) <=
            norm (typeISourceSmoothBlock Y A r sigma t)) ->
        (ApproxAddEnergy 1 W : Real) <=
          T ^ zetaExtract * ((2 : Real) ^ Pcap * T ^ beta) ^ e := by
  have hsigmaStrictUpper : sigma < 1 := hsigmaUpper.trans_lt (by norm_num)
  have hdHalf : d <= 1 / 2 := by
    have hGap : sigma - 1 / 2 <= 1 / 4 := by linarith
    norm_num at hdGap hGap ⊢
    nlinarith [hdGap]
  have hdOne : d <= 1 := hdHalf.trans (by norm_num)
  obtain ⟨Treflect, hTreflect, hReflect⟩ :=
    eventually_interior_source_family_reflected_energy hsigma
      hsigmaStrictUpper hd hdOne hdGap hu huD
  have hCells := eventually_interior_reflected_physical_cell hsigma
    hsigmaUpper hd hdGap huD hepsilon heta hzetaShell hzetaReflect
    hzetaPower hzetaDil hloss hzetaRel hzetaCard hRelMargin
    hsigma0Lower hsigma0Upper hBudget hEffective
  have hClog := eventually_const_mul_sharp_cutoff_clog_le_rpow
    (D := (1 : Real)) (zeta := v) (by norm_num) hv
  have hExtraction := eventually_reflectedExtractionLoss_le_rpow
    hd.le hzetaExtract
  dsimp only
  filter_upwards [hCells, hClog, hExtraction,
      eventually_ge_atTop Treflect, eventually_ge_atTop (8 : Real)]
    with T hCellsT hClogT hExtractionT hTreflectT hTEight
  intro tau Y A r W hA hY hr hUpper hTau hTauOne hTauTwo hW hSep
    hRange hLarge
  let Q : Nat := 2 ^ r * Y
  let M : Nat := mediumTypeIDualCutoff T d Q
  let V : Real := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : Nat)
  let Rdet : Real := (Real.pi * V) /
    (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : Real := Rdet / (2 * (M : Real) ^ sigma)
  let e : Real := max (heathBrownLowFirstSlope sigma0)
      (heathBrownLowSecondSlope sigma0) +
    4 * (zetaRel + heathBrownCardinalityShift zetaCard)
  have hPowFour : 4 <= 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFourY : 4 * Y <= Q := by
    dsimp only [Q]
    exact Nat.mul_le_mul_right Y hPowFour
  have hLowerNat : Y + 1 <= Q / 2 := by omega
  have hLower : ((Y + 1 : Nat) : Real) <= (Q : Real) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 2)).2
    exact_mod_cast (show (Y + 1) * 2 <= Q by omega)
  have hQOne : 1 < Q := by
    have : 4 <= Q := by
      calc
        4 = 4 * 1 := by omega
        _ <= 4 * Y := Nat.mul_le_mul_left 4 hY
        _ <= Q := hQFourY
    omega
  have hTPos : 0 < T := by linarith
  have hScale : (Q : Real) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hReflected := hReflect W hTreflectT hA hY hr hLower hUpper hTau
    hTauOne hTauTwo hW hSep hRange hLarge
  dsimp only [Q, M, V, Rdet, S] at hReflected
  obtain ⟨hMOne, ⟨out⟩⟩ := hReflected
  have hMPos : 0 < M := by
    have : 1 < M := by simpa only [M, Q] using hMOne
    omega
  have hMSharp : M <= Nat.floor (sharpZetaCutoff T) := by
    simpa only [M, Q] using
      mediumTypeIDualCutoff_le_sharpZetaCutoff hTEight hd.le hdHalf
        hQOne (by linarith) hTauTwo hScale
  have hClogM : Nat.clog 2 M <=
      Nat.clog 2 (Nat.floor (sharpZetaCutoff T)) :=
    Nat.clog_mono_right 2 hMSharp
  have hClogPower : (Nat.clog 2 M : Real) <= T ^ v := by
    calc
      (Nat.clog 2 M : Real) <=
          (Nat.clog 2 (Nat.floor (sharpZetaCutoff T)) : Real) := by
        exact_mod_cast hClogM
      _ = 1 * (Nat.clog 2 (Nat.floor (sharpZetaCutoff T)) : Real) := by ring
      _ <= T ^ v := hClogT
  have hEveryCell : forall i j : Fin 4,
      (ApproxAddEnergy 1 (out.U i j) : Real) <=
        ((2 : Real) ^ reflectedPhysicalPowerCap d (2 / ((sigma - 1 / 2) / 2)) *
            T ^ reflectedPhysicalBeta d) ^ e := by
    intro i j
    by_cases hNonempty : (out.U i j).Nonempty
    · have hCell := hCellsT hA hY hr hUpper hTau hTauOne hTauTwo
        (out.label i j) (out.U i j) hNonempty (out.hDyadicSeparated i j)
        (out.hDyadicRange i j)
        (by
          intro n hn
          exact norm_normalizedTypeIReflectedCoeff_le_one
            (by linarith : 0 <= sigma) hMPos)
        (out.hDyadicLarge i j)
      simpa only [e] using hCell
    · have hEmpty : out.U i j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNonempty
      rw [hEmpty]
      simp only [ApproxAddEnergy, approximateAdditiveQuadruples,
        Finset.product_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact Real.rpow_nonneg (by positivity) _
  have hRaw := out.energy_le_of_all_cells hEveryCell
  have hLoss := hExtractionT (Nat.clog 2 M) hClogPower
  have hEnergyNonneg : 0 <=
      ((2 : Real) ^ reflectedPhysicalPowerCap d (2 / ((sigma - 1 / 2) / 2)) *
          T ^ reflectedPhysicalBeta d) ^ e := Real.rpow_nonneg (by positivity) _
  calc
    (ApproxAddEnergy 1 W : Real) <=
        16 * ((doubleFloorDefectWindow 1).card : Real) *
          reflectedDyadicExtractionFactor (T ^ d) (Nat.clog 2 M) *
          ((2 : Real) ^ reflectedPhysicalPowerCap d (2 / ((sigma - 1 / 2) / 2)) *
            T ^ reflectedPhysicalBeta d) ^ e := hRaw
    _ <= T ^ zetaExtract *
          ((2 : Real) ^ reflectedPhysicalPowerCap d (2 / ((sigma - 1 / 2) / 2)) *
            T ^ reflectedPhysicalBeta d) ^ e := by
      exact mul_le_mul_of_nonneg_right hLoss hEnergyNonneg

#print axioms eventually_interior_source_family_reflected_physical_bound

end

end GafniTao
