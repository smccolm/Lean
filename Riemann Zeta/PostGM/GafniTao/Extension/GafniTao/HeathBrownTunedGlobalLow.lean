import GafniTao.HeathBrownTunedColorEnvelope
import GafniTao.HeathBrownMixedSourceAssembly
import GafniTao.HeathBrownFullyUniformGlobalSourceAlternative
import GafniTao.HeathBrownGlobalBoundedEnvelope

/-!
# Global low-range Heath--Brown source assembly

The selected dyadic shells are routed either to the literal bounded-shell
majorant or through four actual classified source colors.  A shell that is
below a cutoff chosen after the common analytic constants is returned to the
bounded branch with an enlarged fixed height.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem exists_eventual_heathBrown_tuned_global_low_majorant
    {sigma epsilon : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hepsilon : 0 < epsilon) :
    ∃ R T0 : Real, 1 <= R ∧ 1 <= T0 ∧
      ∀ T : Real, T0 <= T ->
        (zeroAdditiveEnergyCount sigma T : Real) <=
          (dyadicZeroShellCount T : Real) ^ 4 *
            max (heathBrownBoundedShellMajorant sigma R T)
              (T ^ (max (heathBrownLowFirstSlope sigma)
                (heathBrownLowSecondSlope sigma) + 2 * epsilon / 3)) := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  have hd := heathBrownTuneD_pos hsigma hepsilon
  have hdelta1 := heathBrownTuneDelta1_pos hsigma
  have hdelta2 := heathBrownTuneDelta2_pos hsigma hepsilon
  have hdelta1Upper : heathBrownTuneDelta1 sigma <= 1 := by
    have hg := heathBrownTuneGap_le_quarter hsigmaUpper
    unfold heathBrownTuneDelta1
    linarith
  have hdelta2Sigma : heathBrownTuneDelta2 sigma epsilon < sigma := by
    have hsmall := heathBrownTuneDelta2_lt_gap hsigma hsigmaUpper hepsilon
    unfold heathBrownTuneGap at hsmall
    linarith
  obtain ⟨K, C, Cp, Cmv, C0, C2, C4, _B0, R0,
      hK, hC, hCp, hCmv, hC0, hC2, hC4, _hB0, hR0, hSource⟩ :=
    exists_heathBrownFullyUniformGlobalSourceAlternative
      hsigma (show sigma <= 1 by linarith) hd
      (show heathBrownTuneD sigma epsilon < 1 by
        have hbound := heathBrownTuneD_le_gap_div_thousand
          (sigma := sigma) (epsilon := epsilon) hsigma hsigmaUpper
        have hg := heathBrownTuneGap_le_quarter hsigmaUpper
        linarith)
      hdelta1 hdelta2
      (heathBrownTuneDelta2_half_le_delta1 hsigma hsigmaUpper hepsilon)
      hdelta1Upper hdelta2Sigma
      (heathBrownTuneCube hsigma hsigmaUpper hepsilon)
      (show 0 < heathBrownTuneEta sigma epsilon by
        unfold heathBrownTuneEta; positivity)
      (show 0 < heathBrownTuneDetectorEpsilon sigma epsilon by
        unfold heathBrownTuneDetectorEpsilon; positivity)
  have hColor := eventually_tuned_actual_source_color_energy_envelope
    (K := K) hsigma hsigmaUpper hepsilon hC
      (zero_lt_one.trans_le hCp) hCmv hC0 hC2 hC4
  obtain ⟨Ucolor, hUcolor⟩ := eventually_atTop.1 hColor
  obtain ⟨Uselect, Tselect, hUselectOne, hTselectOne, hSelection⟩ :=
    exists_heathBrown_mixed_selection_loss_cutoff
      (delta := heathBrownTuneD sigma epsilon)
      (delta1 := heathBrownTuneDelta1 sigma)
      (v := heathBrownTuneD sigma epsilon)
      (zeta := heathBrownTuneSelection sigma epsilon)
      hd.le hdelta1 hd (by
        unfold heathBrownTuneSelection
        linarith)
  let Umin := max 1 (max Ucolor Uselect)
  let R := max R0 (2 * Umin)
  let e := max (heathBrownLowFirstSlope sigma)
      (heathBrownLowSecondSlope sigma) + epsilon / 3
  let z := heathBrownTuneSelection sigma epsilon
  let target := max (heathBrownLowFirstSlope sigma)
      (heathBrownLowSecondSlope sigma) + 2 * epsilon / 3
  have hLNonneg := heathBrownLowMaxSlope_nonneg hsigmaUpper
  have he : 0 <= e := by dsimp only [e]; linarith
  have hz : 0 < z := by
    dsimp only [z]
    unfold heathBrownTuneSelection
    positivity
  have hztarget : z + e < target := by
    have hqEpsilon := heathBrownTuneQ_le_epsilon
      (sigma := sigma) (epsilon := epsilon)
    have hg := heathBrownTuneGap_le_quarter hsigmaUpper
    dsimp only [z, e, target]
    unfold heathBrownTuneSelection heathBrownTuneD
    nlinarith
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (2 : Real) ^ e) (a := z + e) (b := target) hztarget
  obtain ⟨Tabs, hTabs⟩ := eventually_atTop.1 hAbsorb
  let T0 := max 1 (max (Real.exp 2) (max 8 (max Tselect Tabs)))
  have hR : 1 <= R := by
    have hUminOne : 1 <= Umin := by
      dsimp only [Umin]
      exact le_max_left _ _
    exact (show 1 <= 2 * Umin by linarith).trans (le_max_right _ _)
  have hT0 : 1 <= T0 := by dsimp only [T0]; exact le_max_left _ _
  refine ⟨R, T0, hR, hT0, ?_⟩
  intro T hT
  have hTone : 1 <= T := hT0.trans hT
  have hTselect : Tselect <= T := by
    calc
      Tselect <= max Tselect Tabs := le_max_left _ _
      _ <= max 8 (max Tselect Tabs) := le_max_right _ _
      _ <= max (Real.exp 2) (max 8 (max Tselect Tabs)) := le_max_right _ _
      _ <= T0 := by dsimp only [T0]; exact le_max_right _ _
      _ <= T := hT
  have hTabsT : Tabs <= T := by
    calc
      Tabs <= max Tselect Tabs := le_max_right _ _
      _ <= max 8 (max Tselect Tabs) := le_max_right _ _
      _ <= max (Real.exp 2) (max 8 (max Tselect Tabs)) := le_max_right _ _
      _ <= T0 := by dsimp only [T0]; exact le_max_right _ _
      _ <= T := hT
  have hExpT : Real.exp 2 <= T := by
    exact (le_max_of_le_right (le_max_left _ _)).trans hT
  have hEightT : 8 <= T := by
    exact (le_max_of_le_right (le_max_of_le_right
      (le_max_left _ _))).trans hT
  have hTCeil : max (Real.exp 2) 8 <= 2 * (Nat.ceil T : Real) := by
    have hCeil : T <= (Nat.ceil T : Real) := Nat.le_ceil T
    have hCeilTwo : (Nat.ceil T : Real) <= 2 * (Nat.ceil T : Real) := by
      have hCeilNonneg : 0 <= (Nat.ceil T : Real) := by positivity
      linarith
    apply max_le
    · exact hExpT.trans (hCeil.trans hCeilTwo)
    · exact hEightT.trans (hCeil.trans hCeilTwo)
  obtain ⟨coverLabel, hCover, hAlternative⟩ := hSource T hTCeil hTone
  have hCoverReal :
      (zeroAdditiveEnergyCount sigma T : Real) <=
        (dyadicZeroShellCount T : Real) ^ 4 *
          (weightedMixedAdditiveEnergyOn
            (dyadicZeroShell sigma T (coverLabel 0))
            (dyadicZeroShell sigma T (coverLabel 1))
            (dyadicZeroShell sigma T (coverLabel 2))
            (dyadicZeroShell sigma T (coverLabel 3))
            zeroMultiplicity 1 : Real) := by
    exact_mod_cast hCover
  apply hCoverReal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases hAlternative with hBounded | hOutput
  · apply hBounded.trans
    apply le_max_of_le_left
    unfold heathBrownBoundedShellMajorant
    have hlog : 0 <= Real.log (2 * (Nat.ceil T : Real)) :=
      Real.log_nonneg (by
        have hCeilOne : 1 <= (Nat.ceil T : Real) := hTone.trans (Nat.le_ceil T)
        linarith)
    have hfactor :
        0 <= 3 * globalLocalZeroLogConstant *
          Real.log (2 * (Nat.ceil T : Real)) :=
      mul_nonneg
        (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le) hlog
    apply mul_le_mul_of_nonneg_right _ hfactor
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast zeroCount_mono_height_sigma
      (sigma := sigma) (T := R0) (R := R) (le_max_left _ _)
  · obtain ⟨out⟩ := hOutput
    let U0 := dyadicZeroShellInnerHeight (coverLabel 0)
    let U1 := dyadicZeroShellInnerHeight (coverLabel 1)
    let U2 := dyadicZeroShellInnerHeight (coverLabel 2)
    let U3 := dyadicZeroShellInnerHeight (coverLabel 3)
    by_cases hLarge : Umin <= U0 ∧ Umin <= U1 ∧ Umin <= U2 ∧ Umin <= U3
    · have hUcolorMin : Ucolor <= Umin :=
        (le_max_left Ucolor Uselect).trans (le_max_right _ _)
      have hUselectMin : Uselect <= Umin :=
        (le_max_right Ucolor Uselect).trans (le_max_right _ _)
      have hUiT (i : Fin 4) :
          dyadicZeroShellInnerHeight (coverLabel i) <= 2 * T :=
        dyadicZeroShellInnerHeight_le_two_mul hTone _
      have hColorBound
          (i : Fin 4)
          {D : ClassicalBinaryShellDetectorData sigma
            (dyadicZeroShellInnerHeight (coverLabel i))
            (heathBrownTuneD sigma epsilon)
            (Nat.floor ((dyadicZeroShellInnerHeight (coverLabel i)) ^
              heathBrownTuneDelta1 sigma))
            (Nat.floor ((dyadicZeroShellInnerHeight (coverLabel i)) ^
              (heathBrownTuneDelta2 sigma epsilon / 2)))
            (Nat.floor (sharpZetaCutoff
              (dyadicZeroShellInnerHeight (coverLabel i))))
            ((dyadicZeroShellInnerHeight (coverLabel i)) ^
              (-heathBrownTuneDelta2 sigma epsilon))}
          {label : Fin (D.kI * 2 + D.kII * 2) × Fin 2}
          (o : HeathBrownFullyUniformSourceColorOutput sigma
            (dyadicZeroShellInnerHeight (coverLabel i))
            (heathBrownTuneD sigma epsilon)
            (heathBrownTuneDelta1 sigma)
            (heathBrownTuneDelta2 sigma epsilon)
            (heathBrownTuneEta sigma epsilon)
            (heathBrownTuneDetectorEpsilon sigma epsilon)
            K C Cp Cmv C0 C2 C4 D label)
          (hne : (classicalBinaryColorFamily D label).Nonempty)
          (hUmin : Umin <= dyadicZeroShellInnerHeight (coverLabel i)) :
          (ApproxAddEnergy 1 (classicalBinaryColorFamily D label) : Real) <=
            (2 * T) ^ e := by
        have hlocal := hUcolor _ (hUcolorMin.trans hUmin) o hne
        exact hlocal.trans (Real.rpow_le_rpow
          (dyadicZeroShellInnerHeight_pos _).le (hUiT i) he)
      have h0 : (ApproxAddEnergy 1
          (classicalBinaryColorFamily out.d0 out.mixed.label0) : Real) <=
          (2 * T) ^ e := by
        by_cases hn : (classicalBinaryColorFamily out.d0 out.mixed.label0).Nonempty
        · obtain ⟨o⟩ := out.mixed.output0 hn
          exact hColorBound 0 o hn hLarge.1
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp [ApproxAddEnergy, approximateAdditiveQuadruples]
          positivity
      have h1 : (ApproxAddEnergy 1
          (classicalBinaryColorFamily out.d1 out.mixed.label1) : Real) <=
          (2 * T) ^ e := by
        by_cases hn : (classicalBinaryColorFamily out.d1 out.mixed.label1).Nonempty
        · obtain ⟨o⟩ := out.mixed.output1 hn
          exact hColorBound 1 o hn hLarge.2.1
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp [ApproxAddEnergy, approximateAdditiveQuadruples]
          positivity
      have h2 : (ApproxAddEnergy 1
          (classicalBinaryColorFamily out.d2 out.mixed.label2) : Real) <=
          (2 * T) ^ e := by
        by_cases hn : (classicalBinaryColorFamily out.d2 out.mixed.label2).Nonempty
        · obtain ⟨o⟩ := out.mixed.output2 hn
          exact hColorBound 2 o hn hLarge.2.2.1
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp [ApproxAddEnergy, approximateAdditiveQuadruples]
          positivity
      have h3 : (ApproxAddEnergy 1
          (classicalBinaryColorFamily out.d3 out.mixed.label3) : Real) <=
          (2 * T) ^ e := by
        by_cases hn : (classicalBinaryColorFamily out.d3 out.mixed.label3).Nonempty
        · obtain ⟨o⟩ := out.mixed.output3 hn
          exact hColorBound 3 o hn hLarge.2.2.2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp [ApproxAddEnergy, approximateAdditiveQuadruples]
          positivity
      have hMixed := out.mixed.energy_le_selection_mul hK hC h0 h1 h2 h3
      have hSel := hSelection (out.mixed.toUniform hK hC) hTselect
        (hUselectMin.trans hLarge.1)
        (hUselectMin.trans hLarge.2.1)
        (hUselectMin.trans hLarge.2.2.1)
        (hUselectMin.trans hLarge.2.2.2)
        (hUiT 0) (hUiT 1) (hUiT 2) (hUiT 3)
      have hMixedT :
          (weightedMixedAdditiveEnergyOn
            (absoluteDyadicZeroSlab sigma U0)
            (absoluteDyadicZeroSlab sigma U1)
            (absoluteDyadicZeroSlab sigma U2)
            (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) <=
              T ^ z * (2 * T) ^ e := by
        exact hMixed.trans (mul_le_mul_of_nonneg_right hSel (by positivity))
      have hRewrite : T ^ z * (2 * T) ^ e =
          (2 : Real) ^ e * T ^ (z + e) := by
        have hTPos : 0 < T := zero_lt_one.trans_le hTone
        rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hTPos.le]
        calc
          T ^ z * ((2 : Real) ^ e * T ^ e) =
              (2 : Real) ^ e * (T ^ z * T ^ e) := by ring
          _ = (2 : Real) ^ e * T ^ (z + e) := by
            congr 1
            exact (Real.rpow_add hTPos z e).symm
      have hSourceBound :
          (weightedMixedAdditiveEnergyOn
            (dyadicZeroShell sigma T (coverLabel 0))
            (dyadicZeroShell sigma T (coverLabel 1))
            (dyadicZeroShell sigma T (coverLabel 2))
            (dyadicZeroShell sigma T (coverLabel 3))
            zeroMultiplicity 1 : Real) <= T ^ target := by
        rw [out.shell_eq 0, out.shell_eq 1, out.shell_eq 2, out.shell_eq 3]
        exact hMixedT.trans (by rw [hRewrite]; exact hTabs T hTabsT)
      exact hSourceBound.trans (le_max_right _ _)
    · have hCases : U0 < Umin ∨ U1 < Umin ∨ U2 < Umin ∨ U3 < Umin := by
        by_cases h0 : Umin <= U0
        · by_cases h1 : Umin <= U1
          · by_cases h2 : Umin <= U2
            · have h3 : ¬ Umin <= U3 := by
                intro h3
                exact hLarge ⟨h0, h1, h2, h3⟩
              exact Or.inr (Or.inr (Or.inr (lt_of_not_ge h3)))
            · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge h2)))
          · exact Or.inr (Or.inl (lt_of_not_ge h1))
        · exact Or.inl (lt_of_not_ge h0)
      have hSmall : ∃ i : Fin 4,
          dyadicZeroShellOuterHeight (coverLabel i) <= R := by
        rcases hCases with h0small | h1small | h2small | h3small
        · refine ⟨0, ?_⟩
          rw [dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero
            (out.noncentral 0)]
          exact (mul_le_mul_of_nonneg_left h0small.le (by norm_num)).trans
            (le_max_right _ _)
        · refine ⟨1, ?_⟩
          rw [dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero
            (out.noncentral 1)]
          exact (mul_le_mul_of_nonneg_left h1small.le (by norm_num)).trans
            (le_max_right _ _)
        · refine ⟨2, ?_⟩
          rw [dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero
            (out.noncentral 2)]
          exact (mul_le_mul_of_nonneg_left h2small.le (by norm_num)).trans
            (le_max_right _ _)
        · refine ⟨3, ?_⟩
          rw [dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero
            (out.noncentral 3)]
          exact (mul_le_mul_of_nonneg_left h3small.le (by norm_num)).trans
            (le_max_right _ _)
      exact (weightedMixed_dyadicZeroShells_le_of_bounded
        (show 0 <= sigma by linarith) hTCeil hTone coverLabel hSmall).trans
          (le_max_left _ _)

#print axioms exists_eventual_heathBrown_tuned_global_low_majorant

end

end GafniTao
