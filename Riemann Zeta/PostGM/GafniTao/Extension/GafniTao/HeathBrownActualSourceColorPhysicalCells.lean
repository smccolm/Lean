import GafniTao.HeathBrownClassifiedSourceCells
import GafniTao.HeathBrownTypeILongTailReassembly
import GafniTao.HeathBrownActualTypeIIPhysicalCells

/-!
# Physical low-cell bound for an actual detector colour

This file dispatches the genuine `ClassicalBinaryTypeIOutput`/Type-II branch
stored in a fully uniform source-colour output.  The Type-I arm passes through
the exact long-tail source decomposition and its exhaustive classified-cell
consumer; the Type-II arm consumes the actual powered packet.  The two
physical majorants remain separate under a maximum.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownTypeIPhysicalMajorant
    (sigma U d zetaExtract sigma0 zetaRel zetaCard : Real)
    (Pcap : Nat) : Real :=
  let e := heathBrownLowCellExponent sigma0 zetaRel zetaCard
  let g := (sigma - 1 / 2) / 2
  let Pref := reflectedPhysicalPowerCap d (2 / g)
  max (((2 : Real) ^ Pcap * (6 * U)) ^ e)
    (U ^ zetaExtract *
      (((2 : Real) ^ Pref * U ^ reflectedPhysicalBeta d) ^ e))

noncomputable def heathBrownTypeIIPhysicalMajorant
    (sigma U eta zetaShell zetaConst zetaDil zetaRel zetaCard delta2 : Real) :
    Real :=
  let P := Nat.ceil (4 / delta2)
  let sigma0 := heathBrownEffectiveSigma sigma eta zetaShell zetaConst
    (P + 1) - zetaDil
  (((2 : Real) ^ P * U) ^
    (max (heathBrownLowFirstSlope sigma0)
      (heathBrownLowSecondSlope sigma0) +
        4 * (zetaRel + heathBrownCardinalityShift zetaCard)))

noncomputable def heathBrownSourceReassemblyFactor (U : Real) : Real :=
  (((Nat.clog 2 (Nat.floor (sharpZetaCutoff U) + 1)) ^ 4 : Nat) : Real) *
    (doubleFloorDefectWindow 1).card

noncomputable def heathBrownLongTailReassemblyFactor (U : Real) : Real :=
  (((Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) + 1) ^ 4 : Nat) : Real) *
    (doubleFloorDefectWindow 1).card

theorem eventually_actual_source_color_physical_low_cells
    {sigma d delta1 delta2 eta epsilon zetaLog zetaPower zetaScale
        zetaDil zetaRel zetaCard sigma0 K C Cp Cmv C0 C2 C4
        zetaShell zetaReflect loss v zetaExtract zetaConst : Real}
    {Pcap : Nat}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hd : 0 < d) (hdGap : d <= (sigma - 1 / 2) / 1000)
    (hdelta2D : delta2 <= d) (huTerminal : delta2 < sigma - 1 / 2)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdelta2Upper : delta2 <= 1)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hzetaLog : 0 < zetaLog) (hzetaPower : 0 < zetaPower)
    (hzetaScale : 0 < zetaScale) (hzetaScaleUpper : zetaScale < 2 / 3)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard) (hzetaConst : 0 < zetaConst)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hWideRelMargin : epsilon < (1 - zetaScale) * zetaRel)
    (hPcap : Pcap = Nat.ceil (4 / delta2))
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Eff : sigma0 <= heathBrownLowerSourceEffectiveSigma
      sigma delta2 eta zetaLog zetaPower zetaDil delta1)
    (hsigma0Wide : sigma0 <= heathBrownWideSourceEffectiveSigma
      sigma delta2 eta zetaLog zetaPower zetaScale zetaDil)
    (hsigma0Upper : sigma0 <= 3 / 4)
    (hScaleNear : 3 * zetaScale <= 1 - sigma0)
    (hzetaShell : 0 < zetaShell) (hzetaReflect : 0 < zetaReflect)
    (hloss : 0 < loss) (hv : 0 < v)
    (hzetaExtract : 4 * v + 5 * d < zetaExtract)
    (hBudget :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      let beta := reflectedPhysicalBeta d
      delta2 + d * (2 * sigma + 1) + beta * zetaShell + zetaReflect <=
        (loss + eta) / Uscale)
    (hEffective :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      sigma0 <= reflectedPhysicalEffectiveSigma sigma loss eta zetaShell
        zetaPower zetaDil d Uscale)
    (hTypeIILower : 1 / 2 <=
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
        (Nat.ceil (4 / delta2) + 1) - zetaDil)
    (hTypeIIUpper :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
        (Nat.ceil (4 / delta2) + 1) - zetaDil <= 3 / 4) :
    ∀ᶠ U : Real in atTop,
      ∀ {D : ClassicalBinaryShellDetectorData sigma U d
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))}
        {label : Fin (D.kI * 2 + D.kII * 2) × Fin 2}
        (_out : HeathBrownFullyUniformSourceColorOutput sigma U d delta1
          delta2 eta epsilon K C Cp Cmv C0 C2 C4 D label),
        (classicalBinaryColorFamily D label).Nonempty ->
        (ApproxAddEnergy 1 (classicalBinaryColorFamily D label) : Real) <=
          (heathBrownLongTailReassemblyFactor U *
            heathBrownSourceReassemblyFactor U) *
            max (heathBrownTypeIPhysicalMajorant sigma U d zetaExtract sigma0
              zetaRel zetaCard Pcap)
              (heathBrownTypeIIPhysicalMajorant sigma U eta zetaShell
                zetaConst zetaDil zetaRel zetaCard delta2) := by
  have hTypeI := eventually_classified_source_family_physical_bound
    (K := K) (C := C)
    hsigma hsigmaUpper hd hdGap (show 0 <= delta2 from hdelta2.le)
    hdelta2D huTerminal hdelta1 hdelta2 hdelta2Upper hdeltaOrder hCube
    heta hepsilon hzetaLog hzetaPower hzetaScale hzetaScaleUpper hzetaDil
    hzetaRel hzetaCard hRelMargin hWideRelMargin hPcap hCp hCmv hC0 hC2 hC4
    hsigma0Lower hsigma0Eff hsigma0Wide hsigma0Upper hScaleNear hzetaShell
    hzetaReflect hloss hv hzetaExtract hBudget hEffective
  have hTypeII := eventually_actualTypeII_physical_low_cells
    (sigma := sigma) (delta := d) (epsilon := epsilon) (C := C)
    (Cp := Cp) (Cmv := Cmv) (C0 := C0) (C2 := C2) (C4 := C4)
    hdelta1 hdelta2 hCube
    (show sigma <= 1 by linarith) heta hzetaShell hzetaConst hzetaDil
    hzetaRel hzetaCard hRelMargin hC hCp hCmv hC0 hC2 hC4
    hTypeIILower hTypeIIUpper
  filter_upwards [hTypeI, hTypeII, eventually_gt_atTop (8 : Real)]
    with U hTypeIU hTypeIIU hUEight
  intro D label out hW
  let A := Nat.floor (sharpZetaCutoff U)
  let F := heathBrownSourceReassemblyFactor U
  let FL := heathBrownLongTailReassemblyFactor U
  let MI := heathBrownTypeIPhysicalMajorant sigma U d zetaExtract sigma0
    zetaRel zetaCard Pcap
  let MII := heathBrownTypeIIPhysicalMajorant sigma U eta zetaShell
    zetaConst zetaDil zetaRel zetaCard delta2
  have hUPos : 0 < U := by linarith
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : Nat))
    apply Nat.le_floor
    exact (show (2 : Real) <= 4 * U by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff U).le
  have hFOne : 1 <= F := by
    dsimp only [F, heathBrownSourceReassemblyFactor]
    have hClog : 1 <= Nat.clog 2 (A + 1) :=
      Nat.clog_pos (by omega) (by omega)
    have hPow : 1 <= Nat.clog 2 (A + 1) ^ 4 := one_le_pow₀ hClog
    have hWindow : 1 <= (doubleFloorDefectWindow 1).card := by
      apply Finset.card_pos.mpr
      exact ⟨0, by simp [doubleFloorDefectWindow]⟩
    have hNat : 1 <= Nat.clog 2 (A + 1) ^ 4 *
        (doubleFloorDefectWindow 1).card := by
      simpa using Nat.mul_le_mul hPow hWindow
    exact_mod_cast hNat
  have hFLOne : 1 <= FL := by
    dsimp only [FL, heathBrownLongTailReassemblyFactor]
    have hClog : 1 <= Nat.clog 2 A + 1 := by omega
    have hPow : 1 <= (Nat.clog 2 A + 1) ^ 4 := one_le_pow₀ hClog
    have hWindow : 1 <= (doubleFloorDefectWindow 1).card := by
      apply Finset.card_pos.mpr
      exact ⟨0, by simp [doubleFloorDefectWindow]⟩
    have hNat : 1 <= (Nat.clog 2 A + 1) ^ 4 *
        (doubleFloorDefectWindow 1).card := by
      simpa using Nat.mul_le_mul hPow hWindow
    exact_mod_cast hNat
  have hMINonneg : 0 <= MI := by
    dsimp only [MI, heathBrownTypeIPhysicalMajorant]
    exact (Real.rpow_nonneg (by positivity) _).trans (le_max_left _ _)
  have hMIINonneg : 0 <= MII := by
    dsimp only [MII, heathBrownTypeIIPhysicalMajorant]
    positivity
  rcases out.branch with hDirect | hPowered
  · have hY : 1 <= Nat.floor (U ^ delta1) := by
      apply Nat.le_floor
      show ((1 : Nat) : Real) <= U ^ delta1
      norm_num
      exact (Real.one_lt_rpow (by linarith) hdelta1).le
    have hDirectBound := hDirect.energy_le_of_classified_sources hY
      (M := F * MI) (by
        intro r W hSub hSep hLarge hClassified
        by_cases hW' : W.Nonempty
        · have hRange : ∀ t ∈ W,
              U - U ^ d <= t ∧ t <= 2 * U + U ^ d := by
            intro t ht
            exact (classicalBinaryColorFamily_oriented_data D label).2.2 t
              (hSub ht)
          have hLarge' : ∀ t ∈ W,
              ((3 / 4 : Real) * (U ^ (-delta2) / 2)) /
                  (Nat.clog 2 A + 1 : Nat) <=
                ‖typeISourceSmoothBlock (Nat.floor (U ^ delta1)) A r sigma t‖ := by
            intro t ht
            have hNumerator : (3 / 4 : Real) * (U ^ (-delta2) / 2) =
                U ^ (-delta2) * (3 / 8) := by ring
            rw [hNumerator]
            exact hLarge t ht
          have hCell := hTypeIU out W hW' hSep hRange hLarge' hClassified
          simpa only [F, MI, heathBrownSourceReassemblyFactor,
            heathBrownTypeIPhysicalMajorant, A] using hCell
        · have hEmpty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW'
          subst W
          simpa [ApproxAddEnergy, approximateAdditiveQuadruples] using
            mul_nonneg (zero_le_one.trans hFOne) hMINonneg)
    have hIMax : MI <= max MI MII := le_max_left _ _
    calc
      (ApproxAddEnergy 1 (classicalBinaryColorFamily D label) : Real) <=
          FL * (F * MI) := by
            simpa only [FL, heathBrownLongTailReassemblyFactor, A] using
              hDirectBound
      _ = (FL * F) * MI := by ring
      _ <= (FL * F) * max MI MII :=
        mul_le_mul_of_nonneg_left hIMax
          (mul_nonneg (zero_le_one.trans hFLOne) (zero_le_one.trans hFOne))
  · obtain ⟨r, hLabel, ⟨full⟩⟩ := hPowered
    have hRaw := hTypeIIU D label r hLabel full hW
    have hRaw' : (ApproxAddEnergy 1 (classicalBinaryColorFamily D label) : Real) <=
        MII := by
      simpa only [MII, heathBrownTypeIIPhysicalMajorant] using hRaw
    have hIImax : MII <= max MI MII := le_max_right _ _
    have hFactorOne : 1 <= FL * F :=
      one_le_mul_of_one_le_of_one_le hFLOne hFOne
    exact hRaw'.trans ((show MII <= (FL * F) * MII by
      nlinarith only [hFactorOne, hMIINonneg]).trans
        (mul_le_mul_of_nonneg_left hIImax (zero_le_one.trans hFactorOne)))

#print axioms eventually_actual_source_color_physical_low_cells

end

end GafniTao
