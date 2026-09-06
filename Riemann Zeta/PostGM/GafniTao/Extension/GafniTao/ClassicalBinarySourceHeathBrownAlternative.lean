import GafniTao.ClassicalBinarySourceSelectedFamily
import GafniTao.ClassicalBinaryHeathBrownAlternative
import GafniTao.HeathBrownSourcePoweredPackets

/-!
# Source-cutoff Heath--Brown alternative for an actual detector colour

This module replaces the fixed fourth-root prototype by the two literal
source cutoffs.  Type-I colours are consumed by the frozen normalized MHH
theorem.  Type-II colours use the physical logarithmic power and the ambient
height `2^ceil(4/delta2) * U`.
-/

namespace GafniTao

noncomputable section

open Filter RiemannZeta.GuthMaynard

/-- A displacement power strictly below one is eventually at most half the
physical height. -/
theorem eventually_rpow_le_half_self
    {delta : Real} (hdelta : delta < 1) :
    exists U0 : Real, 2 <= U0 /\ forall U : Real, U0 <= U ->
      U ^ delta <= U / 2 := by
  have hGap : 0 < 1 - delta := by linarith
  have hTend : Tendsto (fun U : Real => U ^ (1 - delta)) atTop atTop :=
    tendsto_rpow_atTop hGap
  have hEventually : ∀ᶠ U : Real in atTop, 2 <= U ^ (1 - delta) :=
    (tendsto_atTop.1 hTend) 2
  rw [eventually_atTop] at hEventually
  obtain ⟨U1, hU1⟩ := hEventually
  let U0 := max 2 U1
  refine ⟨U0, le_max_left _ _, ?_⟩
  intro U hU
  have hUTwo : 2 <= U := (le_max_left _ _).trans hU
  have hUPos : 0 < U := by linarith
  have hGrowth := hU1 U ((le_max_right _ _).trans hU)
  have hDeltaNonneg : 0 <= U ^ delta := (Real.rpow_pos_of_pos hUPos _).le
  have hProduct : 2 * U ^ delta <= U := by
    calc
      2 * U ^ delta <= U ^ (1 - delta) * U ^ delta :=
        mul_le_mul_of_nonneg_right hGrowth hDeltaNonneg
      _ = U := by
        rw [← Real.rpow_add hUPos]
        norm_num
  linarith

/-- Every actual nonempty source-cutoff colour is consumed by the precise
Type-I MHH branch or by arbitrary-power Heath--Brown packets. -/
theorem eventually_classicalBinaryColorFamily_source_heathBrown_alternative_native
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 <= sigma)
    (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hdelta1Upper : delta1 <= 1)
    (hCubeExponent : 3 * (delta1 + delta2 / 2) <= 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := Nat.floor (U ^ (delta2 / 2))
      let Y := Nat.floor (U ^ delta1)
      let A := Nat.floor (sharpZetaCutoff U)
      let q0 := U ^ (-delta2)
      forall (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2),
        (classicalBinaryColorFamily d label).Nonempty ->
        exists K C : Real, 0 < K /\ 0 < C /\
          let N := classicalBinarySelectedN Y X d.kI d.kII label.1
          let a := classicalBinarySelectedCoeff A Y X d.kI d.kII
            sigma eta C label.1
          let L := classicalBinarySelectedThreshold Y X d.kI d.kII
            sigma q0 eta C label.1
          let p := heathBrownSourcePower N U
          let P := Nat.ceil (4 / delta2)
          let R := 2 * U + U ^ delta
          0 < N /\
          (forall n, n ∈ dyadicInterval N -> ‖a n‖ <= 1) /\
          (forall t, t ∈ classicalBinaryColorFamily d label ->
            L <= ‖sourceDirichletPoly N a t‖) /\
          (ClassicalBinaryTypeIOutput K sigma U delta q0 Y X A d label \/
            (Nonempty (HeathBrownPoweredEnergyPacket epsilon
                ((2 ^ P : Real) * U) R N p eta L
                (classicalBinaryColorFamily d label) a) /\
              Nonempty (HeathBrownPoweredCardinalityPacket
                ((2 ^ P : Real) * U) R N p eta L
                (classicalBinaryColorFamily d label) a) /\
              Nonempty (HeathBrownPoweredCardinalityPacket
                ((2 ^ P : Real) * U) R N (p + 1) eta L
                (classicalBinaryColorFamily d label) a))) := by
  obtain ⟨Uscale, hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCubeExponent
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  obtain ⟨Ushift, hUshift, hShift⟩ :=
    eventually_rpow_le_half_self hdeltaUpper
  let U0 := max Uscale (max Ucut Ushift)
  refine ⟨U0, hUscale.trans (le_max_left _ _), ?_⟩
  intro U hU
  dsimp only
  let X := Nat.floor (U ^ (delta2 / 2))
  let Y := Nat.floor (U ^ delta1)
  let A := Nat.floor (sharpZetaCutoff U)
  let q0 := U ^ (-delta2)
  intro d label hW
  have hUscale' : Uscale <= U := (le_max_left _ _).trans hU
  have hRest : max Ucut Ushift <= U := (le_max_right _ _).trans hU
  have hUcut' : Ucut <= U := (le_max_left _ _).trans hRest
  have hUshift' : Ushift <= U := (le_max_right _ _).trans hRest
  have hCutData := hCut U hUcut'
  dsimp only at hCutData
  have hX : 0 < X := by simpa only [X] using hCutData.1
  have hY : 0 < Y := by
    have : 1 < Y := by simpa only [Y] using hCutData.2.1
    omega
  have hXY : X <= Y := by simpa only [X, Y] using hCutData.2.2.1
  have hUOne : 1 <= U := by linarith [hUscale.trans hUscale']
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hq0 : 0 < q0 := by
    dsimp only [q0]
    exact Real.rpow_pos_of_pos hUPos _
  obtain ⟨K, hK, hMHH⟩ := classicalBinaryColorFamily_typeI_mhh_native
  obtain ⟨C, hC, hCoeff⟩ := sharpMollifiedCoeff_bound eta heta
  have hData := classicalBinarySourceSelectedFamily_alternative d label
    hY hX hq0 hC heta.le hsigma (fun n hn => hCoeff Y X n hn) hW
  dsimp only at hData
  refine ⟨K, C, hK, hC, hData.1, hData.2.1, hData.2.2.1, ?_⟩
  rcases hData.2.2.2 with hTypeI | hTypeII
  · left
    obtain ⟨r, hrLabel, hrLower, hrUpper⟩ := hTypeI
    refine ⟨r, hrLabel, ?_, ?_, ?_⟩
    · have hLowerY : Y <= classicalTypeIShellScaleN Y r := by
        simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
          hrLower
      exact hXY.trans hLowerY
    · simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
        hrUpper
    · have hNr : 0 < classicalTypeIShellScaleN Y r := by
        simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
          hData.1
      exact hMHH d label r hrLabel hsigma (by linarith) hq0
        (hShift U hUshift') hNr
  · right
    obtain ⟨r, hrLabel, _hrLower, _hrUpper⟩ := hTypeII
    have hScaleData := hScale U hUscale' (by rw [d.hkII_eq]) label.1 r hrLabel
    dsimp only [X, Y] at hScaleData
    let N := classicalBinarySelectedN Y X d.kI d.kII label.1
    let p := heathBrownSourcePower N U
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    have hpThree : 3 <= p := by simpa only [N, p] using hScaleData.2.2.2.2.1
    have hp : 0 < p := by omega
    have hpP : p <= P := by
      simpa only [N, p, P] using hScaleData.2.2.2.2.2.2.2.2
    have hPowDelta : U ^ delta <= U := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
    have hTwoPow : (8 : Real) <= (2 : Real) ^ P := by
      have hNat : 2 ^ 3 <= 2 ^ P :=
        Nat.pow_le_pow_right (by omega) (hpThree.trans hpP)
      exact_mod_cast hNat
    have hRB : 2 * R <= (2 ^ P : Real) * U := by
      dsimp only [R]
      have hU0 : 0 <= U := hUPos.le
      calc
        2 * (2 * U + U ^ delta) <= 8 * U := by nlinarith
        _ <= (2 : Real) ^ P * U :=
          mul_le_mul_of_nonneg_right hTwoPow hU0
    have hkIProduct : 0 < d.kI * 2 := d.hkI
    have hkIIProduct : 0 < d.kII * 2 := d.hkII
    have hkI : 0 < d.kI := by omega
    have hkII : 0 < d.kII := by omega
    have hPackets := finite_source_arbitrary_power_packets_native
      epsilon U R eta
      (classicalBinarySelectedThreshold Y X d.kI d.kII
        sigma q0 eta C label.1)
      N p P (classicalBinaryColorFamily d label)
      (classicalBinarySelectedCoeff A Y X d.kI d.kII
        sigma eta C label.1)
      hepsilon hUOne (by simpa only [N] using hData.1) hp hpP hRB
      (by simpa only [N, p] using hScaleData.2.2.2.2.2.1)
      heta
      (classicalBinarySelectedThreshold_pos hY hX hkI hkII
        hq0 hC label.1)
      (classicalBinaryColorFamily_separated d label)
      (classicalBinaryColorFamily_in_symmetric_shell d label)
      hData.2.1 hData.2.2.1
    simpa only [N, p, P, R] using hPackets

#print axioms eventually_rpow_le_half_self
#print axioms eventually_classicalBinaryColorFamily_source_heathBrown_alternative_native

end

end GafniTao
