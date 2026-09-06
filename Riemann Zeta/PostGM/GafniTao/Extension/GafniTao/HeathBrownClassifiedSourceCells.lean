import GafniTao.HeathBrownClassifiedSourceReassembly
import GafniTao.HeathBrownLowerSourceCell
import GafniTao.HeathBrownWideSourceCell
import GafniTao.HeathBrownSquareSourceCell
import GafniTao.HeathBrownTransitionSourceCell
import GafniTao.HeathBrownInteriorReflectedBound
import GafniTao.ClassicalBinaryFullyUniformSourceAlternative

/-!
# Actual analytic cells for every classified Type-I source

This file instantiates the exhaustive finite reassembly theorem with the
fully uniform packets carried by an actual classical-binary detector colour.
The four dyadic cases and the reflected case remain visible in the bound.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownLowCellExponent
    (sigma0 zetaRel zetaCard : Real) : Real :=
  max (heathBrownLowFirstSlope sigma0)
      (heathBrownLowSecondSlope sigma0) +
    4 * (zetaRel + heathBrownCardinalityShift zetaCard)

theorem heathBrownLowCellExponent_nonneg
    {sigma0 zetaRel zetaCard : Real}
    (hsigma0Upper : sigma0 <= 3 / 4)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard) :
    0 <= heathBrownLowCellExponent sigma0 zetaRel zetaCard := by
  have hden : 0 < 2 - sigma0 := by linarith
  have hnum : 0 <= 10 - 11 * sigma0 := by linarith
  have hfirst : 0 <= heathBrownLowFirstSlope sigma0 := by
    unfold heathBrownLowFirstSlope
    exact div_nonneg hnum hden.le
  have hshift : 0 <= heathBrownCardinalityShift zetaCard := by
    unfold heathBrownCardinalityShift
    positivity
  unfold heathBrownLowCellExponent
  exact add_nonneg (hfirst.trans (le_max_left _ _))
    (mul_nonneg (by norm_num) (add_nonneg hzetaRel hshift))

/- The reflected term below uses its own physical power cap and beta.  Keeping
it as a separate argument avoids identifying it with the dyadic source cap. -/
theorem eventually_classified_source_family_physical_bound
    {sigma d delta1 delta2 u eta epsilon zetaLog zetaPower zetaScale
        zetaDil zetaRel zetaCard sigma0 K C Cp Cmv C0 C2 C4
        zetaShell zetaReflect loss v zetaExtract : Real}
    {Pcap : Nat}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hd : 0 < d) (hdGap : d <= (sigma - 1 / 2) / 1000)
    (hu : 0 <= u) (huD : u <= d) (huTerminal : u < sigma - 1 / 2)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdelta2Upper : delta2 <= 1)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hzetaLog : 0 < zetaLog) (hzetaPower : 0 < zetaPower)
    (hzetaScale : 0 < zetaScale) (hzetaScaleUpper : zetaScale < 2 / 3)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hWideRelMargin : epsilon < (1 - zetaScale) * zetaRel)
    (hPcap : Pcap = Nat.ceil (4 / delta2))
    (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Eff : sigma0 <= heathBrownLowerSourceEffectiveSigma
      sigma u eta zetaLog zetaPower zetaDil delta2)
    (hsigma0Wide : sigma0 <= heathBrownWideSourceEffectiveSigma
      sigma u eta zetaLog zetaPower zetaScale zetaDil)
    (hsigma0Upper : sigma0 <= 3 / 4)
    (hScaleNear : 3 * zetaScale <= 1 - sigma0)
    (hzetaShell : 0 < zetaShell) (hzetaReflect : 0 < zetaReflect)
    (hloss : 0 < loss) (hv : 0 < v)
    (hzetaExtract : 4 * v + 5 * d < zetaExtract)
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
    ∀ᶠ U : Real in atTop,
      let Y := Nat.floor (U ^ delta1)
      let A := Nat.floor (sharpZetaCutoff U)
      let e := heathBrownLowCellExponent sigma0 zetaRel zetaCard
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      let beta := reflectedPhysicalBeta d
      let Pref := reflectedPhysicalPowerCap d Uscale
      let M := max (((2 : Real) ^ Pcap * (6 * U)) ^ e)
        (U ^ zetaExtract * (((2 : Real) ^ Pref * U ^ beta) ^ e))
      ∀ {D : ClassicalBinaryShellDetectorData sigma U d
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))}
        {label : Fin (D.kI * 2 + D.kII * 2) × Fin 2}
        (_out : HeathBrownFullyUniformSourceColorOutput sigma U d delta1
          delta2 eta epsilon K C Cp Cmv C0 C2 C4 D label)
        {r : Nat} (W : Finset Real),
        W.Nonempty -> IsSeparated 1 W ->
        (∀ t, t ∈ W -> U - U ^ d <= t ∧ t <= 2 * U + U ^ d) ->
        (∀ t, t ∈ W ->
          ((3 / 4 : Real) * (U ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : Nat) <=
            ‖typeISourceSmoothBlock Y A r sigma t‖) ->
        (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
          (((Y + 1 : Nat) : Real) <= ((2 ^ r * Y : Nat) : Real) / 2 ∧
            2 * (2 ^ r * Y) <= A)) ->
        (ApproxAddEnergy 1 W : Real) <=
          (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
            (doubleFloorDefectWindow 1).card * M := by
  have hPcapOne : 1 <= Pcap := by
    rw [hPcap]
    have hreal : (1 : Real) <= 4 / delta2 := by
      rw [le_div_iff₀ hdelta2]
      linarith
    exact_mod_cast hreal.trans (Nat.le_ceil (4 / delta2))
  have hdOne : d < 1 := by
    have hsigmaGap : sigma - 1 / 2 <= 1 / 4 := by linarith
    nlinarith [hdGap]
  obtain ⟨Udisp, _hUdisp, hDisp⟩ := eventually_rpow_le_half_self hdOne
  have hsigmaNonneg : 0 <= sigma := by linarith
  have hsigmaOne : sigma <= 1 := hsigmaUpper.trans (by norm_num)
  have hLowerCell := eventually_lower_source_dyadic_physical_cell
    (delta := d) hdelta1 hdelta2 hdeltaOrder hCube hsigmaNonneg
      hsigmaOne hu heta hzetaLog hzetaPower hzetaDil hzetaRel hzetaCard
      hRelMargin hPcap hCp hCmv hC0 hC2 hC4 hsigma0Lower hsigma0Eff
      hsigma0Upper
  have hWideCell := eventually_wide_source_dyadic_physical_cell
    (delta := d) hsigmaNonneg hsigmaOne hu heta hzetaLog hzetaPower
      hzetaScale hzetaScaleUpper hzetaDil hzetaRel hzetaCard hScaleNear
      hWideRelMargin hPcapOne hCp hCmv hC0 hC2 hC4
      hsigma0Lower hsigma0Wide hsigma0Upper
  have hSquareCell := eventually_square_source_dyadic_physical_cell
    (delta := d) hdelta2 hsigmaNonneg hsigmaOne hu heta hzetaLog hzetaPower
      hzetaDil hzetaRel hzetaCard hRelMargin hPcap hCp hCmv hC0 hC2 hC4
      hsigma0Lower hsigma0Eff hsigma0Upper
  have hTransitionCell := eventually_transition_source_dyadic_physical_cell
    (delta := d) hdelta2 hdelta2Upper hsigmaNonneg hsigmaOne hu heta
      hzetaLog hzetaPower hzetaDil hzetaRel hzetaCard hRelMargin hPcap
      hCp hCmv hC0 hC2 hC4 hsigma0Lower hsigma0Eff hsigma0Upper
  have hReflected := eventually_interior_source_family_reflected_physical_bound
    hsigma hsigmaUpper hd hdGap hu huD hepsilon heta hzetaShell
      hzetaReflect hzetaPower hzetaDil hloss hzetaRel hzetaCard hRelMargin
      hsigma0Lower hsigma0Upper hv hzetaExtract hBudget hEffective
  have hLowerScale := eventually_heathBrown_lower_source_scale hdelta1
    hdelta2 hdeltaOrder hCube
  have hDyadicLower := eventually_source_dyadic_lower_scale hdelta2 hdeltaOrder
  obtain ⟨Uterminal, hUterminal, hTerminal⟩ :=
    eventually_no_terminal_classified_source (d := d) hsigma huTerminal
  filter_upwards [hLowerCell, hWideCell, hSquareCell, hTransitionCell,
      hReflected, hLowerScale, hDyadicLower,
      eventually_ge_atTop Udisp, eventually_ge_atTop Uterminal,
      eventually_ge_atTop (8 : Real)]
    with U hLowerCellU hWideCellU hSquareCellU hTransitionCellU
      hReflectedU hLowerScaleU hDyadicLowerU hUDisp hUTerminal hUEight
  dsimp only
  intro D label out r W hW hSep hRange hLarge hClassified
  let Y := Nat.floor (U ^ delta1)
  let A := Nat.floor (sharpZetaCutoff U)
  let e := heathBrownLowCellExponent sigma0 zetaRel zetaCard
  let g := (sigma - 1 / 2) / 2
  let Uscale := 2 / g
  let beta := reflectedPhysicalBeta d
  let Pref := reflectedPhysicalPowerCap d Uscale
  let M := max (((2 : Real) ^ Pcap * (6 * U)) ^ e)
    (U ^ zetaExtract * (((2 : Real) ^ Pref * U ^ beta) ^ e))
  have hUPos : 0 < U := by linarith
  have hUOne : 1 < U := by linarith
  have hYPosReal : 0 < (Y : Real) := by
    have hpow : 1 < U ^ delta1 := Real.one_lt_rpow hUOne hdelta1
    have hfloor : (1 : Nat) <= Nat.floor (U ^ delta1) := by
      apply Nat.le_floor
      show ((1 : Nat) : Real) <= U ^ delta1
      norm_num
      exact hpow.le
    exact_mod_cast hfloor
  have hYPos : 0 < Y := by exact_mod_cast hYPosReal
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : Nat))
    apply Nat.le_floor
    exact (show (2 : Real) <= 4 * U by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff U).le
  have hPcapTwo : 2 <= Pcap := by
    rw [hPcap]
    have hreal : (2 : Real) <= 4 / delta2 := by
      rw [le_div_iff₀ hdelta2]
      linarith
    exact_mod_cast hreal.trans (Nat.le_ceil (4 / delta2))
  have heNonneg : 0 <= e := by
    exact heathBrownLowCellExponent_nonneg hsigma0Upper hzetaRel.le hzetaCard.le
  have hMNonneg : 0 <= M := by
    dsimp only [M]
    exact (Real.rpow_nonneg (by positivity) e).trans (le_max_left _ _)
  have hThresholdPos : ∀ s : Nat, 0 <
      (((((2 ^ s * Y : Nat) : Real) / 2) ^ sigma) *
        (((3 / 4 : Real) * (U ^ (-u) / 2)) /
          (Nat.clog 2 A + 1 : Nat))) /
        (Nat.clog 2 (A + 1) : Real) := by
    intro s
    have hQ : 0 < 2 ^ s * Y := Nat.mul_pos (pow_pos (by omega) s) hYPos
    have hClog : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos (by omega) (by omega)
    positivity
  have hSymm : ∀ t, t ∈ W ->
      -(2 * U + U ^ d) <= t ∧ t <= 2 * U + U ^ d := by
    intro t ht
    have htRange := hRange t ht
    constructor
    · have hpow : 0 <= U ^ d := Real.rpow_nonneg hUPos.le d
      linarith
    · exact htRange.2
  have hTerminalLocal : 2 <= r -> A < 2 * (2 ^ r * Y) -> False := by
    intro hrTwo hrA
    exact hTerminal U Y A r W hUTerminal rfl hYPos hrTwo hrA hW hSep
      hLarge hRange (hDisp U hUDisp)
  apply classified_source_family_energy_le hUPos hYPos hAOne hSep hRange
    hLarge hClassified hMNonneg hTerminalLocal
  · intro P W' hSub hrLower hPUpper hPLower hW' hSep' hRange' hLarge'
    let a := conjugateCoeffs
      (normalizedTypeISourceDirichletCoeff Y A r sigma)
    let L : Real := (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
      (((3 / 4 : Real) * (U ^ (-u) / 2)) /
        (Nat.clog 2 A + 1 : Nat))) /
      (Nat.clog 2 (A + 1) : Real)
    let p := heathBrownSourcePower P U
    have hScale := hLowerScaleU (r := r) (P := P) hrLower hPUpper hPLower
    obtain ⟨hPOne, _hPLower, hpTwo, hPow, _hNext, _hCube, hpCap⟩ := hScale
    have hL : 0 < L := by simpa only [L] using hThresholdPos r
    have hCoeff : ∀ n ∈ dyadicInterval P, ‖a n‖ <= 1 := by
      intro n _hn
      simp only [a, norm_conjugateCoeffs]
      exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r sigma
        hsigmaNonneg n
    have hLargeSource : ∀ t ∈ W', L <= ‖sourceDirichletPoly P a t‖ := by
      intro t ht
      simp only [a, norm_sourceDirichletPoly_conjugateCoeffs]
      exact hLarge' t ht
    obtain ⟨full⟩ := out.powered P p L W' a hPOne.le (by omega) hpCap hPow hL
      hSep' (fun t ht => hSymm t (hSub ht)) hCoeff hLargeSource
    have full' : HeathBrownFullyUniformOutputs epsilon
        ((2 : Real) ^ Pcap * U) (2 * U + U ^ d) P p eta L W' a
        Cp Cmv C0 C2 C4 := by
      simpa only [hPcap] using full
    have hCell := hLowerCellU W' a L full' hrLower hPUpper hPLower hW' hL rfl
    apply hCell.trans
    apply (Real.rpow_le_rpow (by positivity) ?_ heNonneg).trans
      (le_max_left _ _)
    gcongr
    nlinarith only [hUPos]
  · intro P W' hSub hUQ hPUpper hPLower hQA hW' hSep' hRange' hLarge'
    let a := conjugateCoeffs
      (normalizedTypeISourceDirichletCoeff Y A r sigma)
    let L : Real := (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
      (((3 / 4 : Real) * (U ^ (-u) / 2)) /
        (Nat.clog 2 A + 1 : Nat))) /
      (Nat.clog 2 (A + 1) : Real)
    have hL : 0 < L := by simpa only [L] using hThresholdPos r
    have hCutNonneg : 0 <= sharpZetaCutoff U := by
      linarith [four_mul_lt_sharpZetaCutoff U]
    have hAUpper : (A : Real) <= 6 * U := by
      dsimp only [A]
      exact (Nat.floor_le hCutNonneg).trans
        (sharpZetaCutoff_le_six_mul (by linarith))
    have hPA : P < A := hPUpper.trans_le hQA
    have hPWide : (P : Real) <= 6 * U := by
      exact (by exact_mod_cast hPA.le : (P : Real) <= A) |>.trans hAUpper
    have hCoeff : ∀ n ∈ dyadicInterval P, ‖a n‖ <= 1 := by
      intro n _hn
      simp only [a, norm_conjugateCoeffs]
      exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r sigma
        hsigmaNonneg n
    have hLargeSource : ∀ t ∈ W', L <= ‖sourceDirichletPoly P a t‖ := by
      intro t ht
      simp only [a, norm_sourceDirichletPoly_conjugateCoeffs]
      exact hLarge' t ht
    obtain ⟨full⟩ := out.wide P L W' a (by omega) hPWide hL hSep'
      (fun t ht => hSymm t (hSub ht)) hCoeff hLargeSource
    have full' : HeathBrownFullyUniformOutputs epsilon
        ((2 : Real) ^ Pcap * (6 * U)) (2 * U + U ^ d) P 1 eta L W' a
        Cp Cmv C0 C2 C4 := by
      simpa only [hPcap] using full
    have hCell := hWideCellU W' a L full' hUQ hPUpper hPLower
      hQA
      hW' hL rfl
    have hTwoPower : 1 <= (2 : Real) ^ Pcap := by
      exact one_le_pow₀ (by norm_num)
    have hSixU : 1 <= 6 * U := by nlinarith only [hUOne]
    have hWideBase : 1 <= (2 : Real) ^ Pcap * (6 * U) :=
      one_le_mul_of_one_le_of_one_le hTwoPower hSixU
    have hWideExp :
        max (heathBrownLowFirstSlope sigma0)
              (heathBrownLowSecondSlope sigma0) +
            4 * (zetaRel + zetaCard) <= e := by
      dsimp only [e, heathBrownLowCellExponent, heathBrownCardinalityShift]
      nlinarith only [hzetaCard]
    exact hCell.trans ((Real.rpow_le_rpow_of_exponent_le hWideBase hWideExp).trans
      (le_max_left _ _))
  · intro P W' hSub hQsq hPsq hPUpper hPLower hW' hSep' hRange' hLarge'
    let a := conjugateCoeffs
      (normalizedTypeISourceDirichletCoeff Y A r sigma)
    let L : Real := (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
      (((3 / 4 : Real) * (U ^ (-u) / 2)) /
        (Nat.clog 2 A + 1 : Nat))) /
      (Nat.clog 2 (A + 1) : Real)
    let p := heathBrownSourcePower P U
    have hPLowerScale := hDyadicLowerU hPLower
    have hPOne : 1 < P := by
      have hone : 1 < U ^ (delta2 / 4) := Real.one_lt_rpow hUOne (by positivity)
      exact_mod_cast hone.trans_le hPLowerScale
    have hPower := heathBrownSourcePower_spec_two hPOne hUPos hPsq
    have hpCap := heathBrownSourcePower_le_ceil_of_rpow_le hPOne hUOne
      hdelta2 hPLowerScale
    have hL : 0 < L := by simpa only [L] using hThresholdPos r
    have hCoeff : ∀ n ∈ dyadicInterval P, ‖a n‖ <= 1 := by
      intro n _hn
      simp only [a, norm_conjugateCoeffs]
      exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r sigma
        hsigmaNonneg n
    have hLargeSource : ∀ t ∈ W', L <= ‖sourceDirichletPoly P a t‖ := by
      intro t ht
      simp only [a, norm_sourceDirichletPoly_conjugateCoeffs]
      exact hLarge' t ht
    obtain ⟨full⟩ := out.powered P p L W' a hPOne.le
      (by dsimp only [p]; omega) (by simpa only [p] using hpCap)
      (by simpa only [p] using hPower.2.1) hL hSep'
      (fun t ht => hSymm t (hSub ht)) hCoeff hLargeSource
    have full' : HeathBrownFullyUniformOutputs epsilon
        ((2 : Real) ^ Pcap * U) (2 * U + U ^ d) P p eta L W' a
        Cp Cmv C0 C2 C4 := by
      simpa only [hPcap] using full
    have hCell := hSquareCellU W' a L full' hPLowerScale hPsq hPUpper hW' hL rfl
    apply hCell.trans
    apply (Real.rpow_le_rpow (by positivity) ?_ heNonneg).trans
      (le_max_left _ _)
    gcongr
    nlinarith only [hUPos]
  · intro P W' hSub hQsq hUPsq hPsqFour hPUpper hPLower hW' hSep'
      hRange' hLarge'
    let a := conjugateCoeffs
      (normalizedTypeISourceDirichletCoeff Y A r sigma)
    let L : Real := (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
      (((3 / 4 : Real) * (U ^ (-u) / 2)) /
        (Nat.clog 2 A + 1 : Nat))) /
      (Nat.clog 2 (A + 1) : Real)
    have hL : 0 < L := by simpa only [L] using hThresholdPos r
    have hCoeff : ∀ n ∈ dyadicInterval P, ‖a n‖ <= 1 := by
      intro n _hn
      simp only [a, norm_conjugateCoeffs]
      exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r sigma
        hsigmaNonneg n
    have hLargeSource : ∀ t ∈ W', L <= ‖sourceDirichletPoly P a t‖ := by
      intro t ht
      simp only [a, norm_sourceDirichletPoly_conjugateCoeffs]
      exact hLarge' t ht
    obtain ⟨full⟩ := out.scaled P 2 L W' a (by omega) (by norm_num)
      (by simpa only [← hPcap] using hPcapTwo) hPsqFour hL hSep'
      (fun t ht => hSymm t (hSub ht))
      hCoeff hLargeSource
    have hPLowerScale := hDyadicLowerU hPLower
    have full' : HeathBrownFullyUniformOutputs epsilon
        ((2 : Real) ^ Pcap * (4 * U)) (2 * U + U ^ d) P 2 eta L W' a
        Cp Cmv C0 C2 C4 := by
      simpa only [hPcap] using full
    have hCell := hTransitionCellU W' a L full' hPLowerScale hUPsq
      hPsqFour hPUpper hW' hL rfl
    apply hCell.trans
    apply (Real.rpow_le_rpow (by positivity) ?_ heNonneg).trans
      (le_max_left _ _)
    gcongr
    nlinarith only [hUPos]
  · intro tau hTau hTauOne hTauTwo hrTwo hQA
    have hRaw := hReflectedU (tau := tau) W rfl hYPos hrTwo hQA hTau
      hTauOne hTauTwo hW hSep hRange hLarge
    have hRawM : (ApproxAddEnergy 1 W : Real) <= M :=
      hRaw.trans (le_max_right _ _)
    have hFactorOne : (1 : Real) <=
        (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card := by
      have hAClog : 1 <= Nat.clog 2 (A + 1) := by
        exact Nat.clog_pos (by omega) (by omega)
      have hpow : 1 <= (Nat.clog 2 (A + 1)) ^ 4 :=
        one_le_pow₀ hAClog
      have hWindow : 1 <= (doubleFloorDefectWindow 1).card := by
        apply Finset.card_pos.mpr
        refine ⟨0, ?_⟩
        simp [doubleFloorDefectWindow]
      have hProductOne : 1 <= (Nat.clog 2 (A + 1)) ^ 4 *
          (doubleFloorDefectWindow 1).card := by
        simpa using Nat.mul_le_mul hpow hWindow
      exact_mod_cast hProductOne
    exact hRawM.trans (by nlinarith only [hFactorOne, hMNonneg])

#print axioms heathBrownLowCellExponent_nonneg
#print axioms eventually_classified_source_family_physical_bound

end

end GafniTao
