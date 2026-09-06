import GafniTao.ClassicalBinaryHeathBrownFamily
import GafniTao.HeathBrownPhysicalPowerChoice
import GafniTao.HeathBrownPoweredSymmetric

/-!
# Powered Heath--Brown output for an actual detector colour

This file closes the finite source-entry boundary for every selected colour
whose scale lies in the physical two-to-four power window.  The input is the
literal colour family produced by the classical binary detector.  The
energy-producing power is selected as two or three, all of its dyadic blocks
fit inside the explicit ambient height `8 * X^4`, and the companion
`(p+1)`-st power is passed to the genuine mean-value theorem.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact finite output of the powered fourth-energy theorem. -/
structure HeathBrownPoweredEnergyPacket
    (epsilon B R : Real) (N p : Nat) (eta L : Real)
    (W : Finset Real) (a : Nat → Complex) where
  Cp : Real
  C0 : Real
  C2 : Real
  C4 : Real
  B0 : Real
  hCp : 0 < Cp
  hC0 : 0 < C0
  hC2 : 0 < C2
  hC4 : 0 < C4
  hB0 : 1 ≤ B0
  consume : B0 ≤ B →
    ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
      (∀ i : Fin 4, Wi i ⊆ gmTranslate R W) ∧
      (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
      (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
      (∀ i : Fin 4, ∀ n ∈ dyadicInterval
          (2 ^ (label i).val * N ^ p),
        ‖sourceNormalizedFinitePoweredCoeffs N p
          (phaseShiftCoeffs R a) Cp eta n‖ ≤ 1) ∧
      (∀ i : Fin 4, ∀ t ∈ Wi i,
        heathBrownPoweredThreshold N p L Cp eta ≤
          ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
            (sourceNormalizedFinitePoweredCoeffs N p
              (phaseShiftCoeffs R a) Cp eta) t‖) ∧
      4 * (ApproxAddEnergy 1 W : Real) ≤
        ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (∑ i : Fin 4,
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L Cp eta)
              (2 ^ (label i).val * N ^ p) (Wi i))

/-- Exact finite output of the companion powered mean-value theorem. -/
structure HeathBrownPoweredCardinalityPacket
    (B R : Real) (N p : Nat) (eta L : Real)
    (W : Finset Real) (a : Nat → Complex) where
  Cp : Real
  Cmv : Real
  hCp : 0 < Cp
  hCmv : 0 < Cmv
  r : Nat
  hr : r ∈ Finset.range p
  W' : Finset Real
  hW' : W' ⊆ W
  hCard : (W.card : Real) ≤ p * (W'.card : Real)
  hUnit : ∀ n ∈ dyadicInterval (2 ^ r * N ^ p),
    ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1
  hLarge : ∀ t ∈ W',
    heathBrownPoweredThreshold N p L Cp eta ≤
      ‖sourceDirichletPoly (2 ^ r * N ^ p)
        (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖
  hMeanValue : (W'.card : Real) ≤
    Cmv * (((2 ^ r * N ^ p : Nat) : Real) ^ 2 /
        (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
      B * ((2 ^ r * N ^ p : Nat) : Real) /
        (heathBrownPoweredThreshold N p L Cp eta) ^ 2)

/-- A detector colour inherits the exact symmetric shell bound. -/
theorem classicalBinaryColorFamily_in_symmetric_shell
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) :
    ∀ t ∈ classicalBinaryColorFamily d label,
      -(2 * U + U ^ delta) ≤ t ∧ t ≤ 2 * U + U ^ delta := by
  intro t ht
  rw [classicalBinaryColorFamily, Finset.mem_image] at ht
  obtain ⟨rho, hrho, rfl⟩ := ht
  exact d.hInterval rho (Finset.mem_filter.mp hrho).1

/-- The exact powered fourth-energy and companion-cardinality outputs for an
actual nonempty detector colour in the physical power window. -/
theorem classicalBinaryColorFamily_powerWindow_heathBrown_native
    {sigma U delta D eta epsilon C : Real} {A : Nat}
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) A (U ^ (-D)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hU : 1 ≤ U)
    (hX : 0 < classicalBinaryHeathBrownCutoff U)
    (hdelta : delta ≤ 1)
    (heta : 0 < eta)
    (hepsilon : 0 < epsilon)
    (hC : 0 < C)
    (hBLower : 16 * U ≤ classicalBinaryHeathBrownHeight U)
    (hN : 0 < classicalBinarySelectedN
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1)
    (hCoeff : ∀ n, n ∈ dyadicInterval
        (classicalBinarySelectedN
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1) →
      ‖classicalBinarySelectedCoeff A
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma eta C
          label.1 n‖ ≤ 1)
    (hLarge : ∀ t ∈ classicalBinaryColorFamily d label,
      classicalBinarySelectedThreshold
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma
          (U ^ (-D)) eta C label.1 ≤
        ‖sourceDirichletPoly
          (classicalBinarySelectedN
            (classicalBinaryHeathBrownCutoff U)
            (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1)
          (classicalBinarySelectedCoeff A
            (classicalBinaryHeathBrownCutoff U)
            (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma eta C
              label.1) t‖)
    (hWindow :
      (classicalBinarySelectedN
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1 : Real) ^ 2 ≤
        classicalBinaryHeathBrownHeight U ∧
      classicalBinaryHeathBrownHeight U ≤
        (classicalBinarySelectedN
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1 : Real) ^ 4) :
    let N := classicalBinarySelectedN
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff A
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma
        (U ^ (-D)) eta C label.1
    let B := classicalBinaryHeathBrownHeight U
    let R := 2 * U + U ^ delta
    let p := heathBrownPhysicalLowPower N B
    Nonempty (HeathBrownPoweredEnergyPacket epsilon (8 * B) R N p eta L
        (classicalBinaryColorFamily d label) a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket (8 * B) R N p eta L
        (classicalBinaryColorFamily d label) a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket (8 * B) R N (p + 1) eta L
        (classicalBinaryColorFamily d label) a) := by
  dsimp only
  let N := classicalBinarySelectedN
    (classicalBinaryHeathBrownCutoff U)
    (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1
  let a := classicalBinarySelectedCoeff A
    (classicalBinaryHeathBrownCutoff U)
    (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma eta C label.1
  let L := classicalBinarySelectedThreshold
    (classicalBinaryHeathBrownCutoff U)
    (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma
      (U ^ (-D)) eta C label.1
  let B := classicalBinaryHeathBrownHeight U
  let R := 2 * U + U ^ delta
  let p := heathBrownPhysicalLowPower N B
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hPowDelta : U ^ delta ≤ U := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU hdelta
  have hBNonneg : 0 ≤ B := by
    dsimp only [B, classicalBinaryHeathBrownHeight]
    positivity
  have hAmbient : 1 ≤ 8 * B := by
    have : 16 ≤ B := by nlinarith
    nlinarith
  have hRB : 2 * R ≤ 8 * B := by
    dsimp only [R]
    nlinarith [hBLower]
  have hp : 0 < p := heathBrownPhysicalLowPower_pos N B
  have hpOne : 0 < p + 1 := Nat.add_pos_left hp 1
  have hkIProduct : 0 < d.kI * 2 := d.hkI
  have hkIIProduct : 0 < d.kII * 2 := d.hkII
  have hkI : 0 < d.kI := by omega
  have hkII : 0 < d.kII := by omega
  have hL : 0 < L := by
    dsimp only [L]
    exact classicalBinarySelectedThreshold_pos hX hX hkI hkII
      (Real.rpow_pos_of_pos hUPos _) hC label.1
  have hSep := classicalBinaryColorFamily_separated d label
  have hSymm := classicalBinaryColorFamily_in_symmetric_shell d label
  have hUpper : ∀ r ∈ Finset.range p,
      (2 ^ r * N ^ p : Real) ≤ 8 * B := by
    intro r hr
    have hNat := heathBrownPhysicalLowPower_selected_length_le
      (N := N) (B := B) hWindow.1 (Finset.mem_range.mp hr)
    have hCast : ((2 ^ r * N ^ p : Nat) : Real) ≤
        (Nat.floor (8 * B) : Real) := by
      exact_mod_cast hNat
    have hReal : ((2 ^ r * N ^ p : Nat) : Real) ≤ 8 * B :=
      hCast.trans (Nat.floor_le (mul_nonneg (by norm_num) hBNonneg))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hReal
  obtain ⟨Cp, C0, C2, C4, B0, hCp, hC0, hC2, hC4, hB0, hEnergy⟩ :=
    finite_symmetric_source_powered_energy_heathBrown_native
      epsilon (8 * B) R N p a eta L (classicalBinaryColorFamily d label)
      hepsilon hN hp heta hL hSep hSymm hRB hCoeff hLarge
  have hEnergyPacket : HeathBrownPoweredEnergyPacket epsilon (8 * B) R
      N p eta L (classicalBinaryColorFamily d label) a := by
    refine ⟨Cp, C0, C2, C4, B0, hCp, hC0, hC2, hC4, hB0, ?_⟩
    intro hThreshold
    exact hEnergy hThreshold hUpper
  obtain ⟨CpBase, CmvBase, hCpBase, hCmvBase, rBase, hrBase,
      WBase, hWBase, hCardBase, hUnitBase, hPoweredBase, hMeanBase⟩ :=
    finite_symmetric_source_powered_cardinality_meanValue_native
      N p (8 * B) R eta L (classicalBinaryColorFamily d label) a
      hN hp hAmbient hRB heta hL hSep hSymm hCoeff hLarge
  have hBaseCardPacket : HeathBrownPoweredCardinalityPacket (8 * B) R
      N p eta L (classicalBinaryColorFamily d label) a :=
    ⟨CpBase, CmvBase, hCpBase, hCmvBase, rBase, hrBase,
      WBase, hWBase, hCardBase, hUnitBase, hPoweredBase, hMeanBase⟩
  obtain ⟨Cp', Cmv, hCp', hCmv, r, hr, W', hW', hCard,
      hUnit, hPowered, hMean⟩ :=
    finite_symmetric_source_powered_cardinality_meanValue_native
      N (p + 1) (8 * B) R eta L (classicalBinaryColorFamily d label) a
      hN hpOne hAmbient hRB heta hL hSep hSymm hCoeff hLarge
  have hCardPacket : HeathBrownPoweredCardinalityPacket (8 * B) R
      N (p + 1) eta L (classicalBinaryColorFamily d label) a :=
    ⟨Cp', Cmv, hCp', hCmv, r, hr, W', hW', hCard,
      hUnit, hPowered, hMean⟩
  exact ⟨⟨hEnergyPacket⟩, ⟨⟨hBaseCardPacket⟩, ⟨hCardPacket⟩⟩⟩

#print axioms classicalBinaryColorFamily_in_symmetric_shell
#print axioms classicalBinaryColorFamily_powerWindow_heathBrown_native

end

end GafniTao
