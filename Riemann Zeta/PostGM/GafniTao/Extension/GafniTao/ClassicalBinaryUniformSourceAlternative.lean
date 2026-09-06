import GafniTao.ClassicalBinarySourceHeathBrownAlternative
import GafniTao.HeathBrownUniformSourcePowered

/-!
# Uniform source-cutoff Heath--Brown alternative

This is the detector-colour alternative with the finite Heath--Brown cutoff
selected before the physical height.  The Type-II branch contains a fully
consumed energy output, not an implication guarded by a locally existential
cutoff.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Source output for one actual detector colour, with the uniform
powered-energy constants fixed by the enclosing eventual theorem. -/
structure HeathBrownUniformSourceColorOutput
    (sigma U delta delta1 delta2 eta epsilon : Real)
    (C0 C2 C4 : Real)
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) where
  K : Real
  C : Real
  hK : 0 < K
  hC : 0 < C
  hN : 0 < classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  hCoeff : ∀ n ∈ dyadicInterval
      (classicalBinarySelectedN
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        d.kI d.kII label.1),
    ‖classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1 n‖ ≤ 1
  hLarge : ∀ t ∈ classicalBinaryColorFamily d label,
    classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1 ≤
      ‖sourceDirichletPoly
        (classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1)
        (classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1) t‖
  branch :
    ClassicalBinaryTypeIOutput K sigma U delta (U ^ (-delta2))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) d label ∨
    let N := classicalBinarySelectedN
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
    let p := heathBrownSourcePower N U
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    Nonempty (HeathBrownUniformPoweredEnergyOutput epsilon
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a C0 C2 C4) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N (p + 1) eta L
        (classicalBinaryColorFamily d label) a)

/-- Every nonempty source detector colour eventually has either the exact
Type-I MHH output or the fully consumed uniform Type-II output. -/
theorem eventually_heathBrownUniformSourceColorOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ C0 C2 C4 B0 U0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧ 8 ≤ U0 ∧
      ∀ U : Real, U0 ≤ U →
        ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
          (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2),
          (classicalBinaryColorFamily d label).Nonempty →
          Nonempty (HeathBrownUniformSourceColorOutput sigma U delta
            delta1 delta2 eta epsilon C0 C2 C4 d label) := by
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hPowered⟩ :=
    finite_source_arbitrary_power_outputs_uniform_native epsilon hepsilon
  obtain ⟨Uscale, hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  obtain ⟨Ushift, hUshift, hShift⟩ :=
    eventually_rpow_le_half_self hdeltaUpper
  let U0 := max B0 (max Uscale (max Ucut Ushift))
  refine ⟨C0, C2, C4, B0, U0, hC0, hC2, hC4, hB0, ?_, ?_⟩
  · exact hUscale.trans
      ((le_max_left Uscale (max Ucut Ushift)).trans
        (le_max_right B0 (max Uscale (max Ucut Ushift))))
  · intro U hU d label hW
    have hB0U : B0 ≤ U := (le_max_left _ _).trans hU
    have hRest : max Uscale (max Ucut Ushift) ≤ U :=
      (le_max_right _ _).trans hU
    have hUscale' : Uscale ≤ U := (le_max_left _ _).trans hRest
    have hCutShift : max Ucut Ushift ≤ U := (le_max_right _ _).trans hRest
    have hUcut' : Ucut ≤ U := (le_max_left _ _).trans hCutShift
    have hUshift' : Ushift ≤ U := (le_max_right _ _).trans hCutShift
    have hCutData := hCut U hUcut'
    dsimp only at hCutData
    have hX : 0 < Nat.floor (U ^ (delta2 / 2)) := hCutData.1
    have hY : 0 < Nat.floor (U ^ delta1) := by omega
    have hXY : Nat.floor (U ^ (delta2 / 2)) ≤ Nat.floor (U ^ delta1) :=
      hCutData.2.2.1
    have hUOne : 1 ≤ U := by linarith [hUscale.trans hUscale']
    have hUPos : 0 < U := zero_lt_one.trans_le hUOne
    have hq0 : 0 < U ^ (-delta2) := Real.rpow_pos_of_pos hUPos _
    obtain ⟨K, hK, hMHH⟩ := classicalBinaryColorFamily_typeI_mhh_native
    obtain ⟨C, hC, hCoeffBound⟩ := sharpMollifiedCoeff_bound eta heta
    have hData := classicalBinarySourceSelectedFamily_alternative d label
      hY hX hq0 hC heta.le hsigma
      (fun n hn => hCoeffBound _ _ n hn) hW
    dsimp only at hData
    refine ⟨⟨K, C, hK, hC, hData.1, hData.2.1, hData.2.2.1, ?_⟩⟩
    rcases hData.2.2.2 with hTypeI | hTypeII
    · left
      obtain ⟨r, hrLabel, hrLower, hrUpper⟩ := hTypeI
      refine ⟨r, hrLabel, ?_, ?_, ?_⟩
      · have hLowerY : Nat.floor (U ^ delta1) ≤
            classicalTypeIShellScaleN (Nat.floor (U ^ delta1)) r := by
          simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
            hrLower
        exact hXY.trans hLowerY
      · simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
          hrUpper
      · have hNr : 0 < classicalTypeIShellScaleN
            (Nat.floor (U ^ delta1)) r := by
          simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
            hData.1
        exact hMHH d label r hrLabel hsigma (by linarith) hq0
          (hShift U hUshift') hNr
    · right
      obtain ⟨r, hrLabel, _hrLower, _hrUpper⟩ := hTypeII
      have hScaleData := hScale U hUscale' (by rw [d.hkII_eq]) label.1 r hrLabel
      let N := classicalBinarySelectedN
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        d.kI d.kII label.1
      let p := heathBrownSourcePower N U
      let P := Nat.ceil (4 / delta2)
      let R := 2 * U + U ^ delta
      have hpThree : 3 ≤ p := by
        simpa only [N, p] using hScaleData.2.2.2.2.1
      have hp : 0 < p := by omega
      have hpP : p ≤ P := by
        simpa only [N, p, P] using hScaleData.2.2.2.2.2.2.2.2
      have hPowDelta : U ^ delta ≤ U := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
      have hTwoPow : (8 : Real) ≤ (2 : Real) ^ P := by
        have hNat : 2 ^ 3 ≤ 2 ^ P :=
          Nat.pow_le_pow_right (by omega) (hpThree.trans hpP)
        exact_mod_cast hNat
      have hRB : 2 * R ≤ (2 ^ P : Real) * U := by
        dsimp only [R]
        calc
          2 * (2 * U + U ^ delta) ≤ 8 * U := by nlinarith
          _ ≤ (2 : Real) ^ P * U :=
            mul_le_mul_of_nonneg_right hTwoPow hUPos.le
      have hL : 0 < classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1 := by
        have hkIProduct : 0 < d.kI * 2 := d.hkI
        have hkIIProduct : 0 < d.kII * 2 := d.hkII
        have hkI : 0 < d.kI := by omega
        have hkII : 0 < d.kII := by omega
        exact classicalBinarySelectedThreshold_pos hY hX hkI hkII hq0 hC label.1
      have hAmbientCutoff : B0 ≤ (2 ^ P : Real) * U := by
        have hOnePow : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
        calc
          B0 ≤ U := hB0U
          _ = 1 * U := by ring
          _ ≤ (2 : Real) ^ P * U :=
            mul_le_mul_of_nonneg_right hOnePow hUPos.le
      have hOutputs := hPowered U R eta
        (classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1)
        N p P (classicalBinaryColorFamily d label)
        (classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1)
        hUOne (by simpa only [N] using hData.1) hp hpP hRB
        (by simpa only [N, p] using hScaleData.2.2.2.2.2.1)
        heta hL (classicalBinaryColorFamily_separated d label)
        (classicalBinaryColorFamily_in_symmetric_shell d label)
        hData.2.1 hData.2.2.1 hAmbientCutoff
      simpa only [N, p, P, R] using hOutputs

#print axioms HeathBrownUniformSourceColorOutput
#print axioms eventually_heathBrownUniformSourceColorOutput

end

end GafniTao
