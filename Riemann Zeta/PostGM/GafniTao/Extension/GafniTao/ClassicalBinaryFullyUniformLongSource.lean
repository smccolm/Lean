import GafniTao.ClassicalBinaryFullyUniformSourceAlternative
import GafniTao.HeathBrownSelectedScaleTwo

/-!
# Fully uniform powered output for every long detector colour

The source energy argument is not intrinsically restricted to a Type-II
label.  Once the selected physical length satisfies `N^2 <= U`, the same
finite powering theorem applies to either detector label.  This file records
that branch-independent consumer.  Short Type-I labels are intentionally not
covered here; they belong to the exact reflection route.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The uniform cap used for the long-colour theorem.  The extra unit gives
an ambient factor at least eight even when the selected source power is two,
which contains the translated symmetric ordinate shell. -/
def heathBrownLongPowerCap (delta2 : Real) : Nat :=
  Nat.ceil (4 / delta2) + 1

/-- Exact powered output attached to one actual detector colour beyond the
physical square threshold. -/
structure HeathBrownFullyUniformLongSourceColorOutput
    (sigma U delta delta1 delta2 eta epsilon : Real)
    (C Cp Cmv C0 C2 C4 : Real)
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) where
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
  hSquare : (classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1 : Real) ^ 2 ≤ U
  scale :
    let N := classicalBinarySelectedN
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII label.1
    let p := heathBrownSourcePower N U
    2 ≤ p ∧ (N : Real) ^ p ≤ U ∧
      U < (N : Real) ^ (p + 1) ∧
      U ^ 2 ≤ ((N : Real) ^ p) ^ 3 ∧
      p ≤ Nat.ceil (4 / delta2)
  outputs :
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
    let P := heathBrownLongPowerCap delta2
    let R := 2 * U + U ^ delta
    Nonempty (HeathBrownFullyUniformOutputs epsilon
      ((2 ^ P : Real) * U) R N p eta L
      (classicalBinaryColorFamily d label) a Cp Cmv C0 C2 C4)

/-- Every nonempty actual detector colour whose selected length satisfies
`N^2 <= U` has fully uniform powered energy and cardinality outputs.  No case
split on the detector label occurs in this theorem. -/
theorem eventually_heathBrownFullyUniformLongSourceColorOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ C Cp Cmv C0 C2 C4 B0 U0 : Real,
      0 < C ∧ 1 ≤ Cp ∧ 0 < Cmv ∧ 0 < C0 ∧ 0 < C2 ∧
      0 < C4 ∧ 1 ≤ B0 ∧ 8 ≤ U0 ∧
      ∀ U : Real, U0 ≤ U →
        ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
          (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2),
          (classicalBinaryColorFamily d label).Nonempty →
          (classicalBinarySelectedN
            (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
            d.kI d.kII label.1 : Real) ^ 2 ≤ U →
          Nonempty (HeathBrownFullyUniformLongSourceColorOutput sigma U delta
            delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label) := by
  obtain ⟨C, hC, hCoeffBound⟩ := sharpMollifiedCoeff_bound eta heta
  let P := heathBrownLongPowerCap delta2
  obtain ⟨Cp, Cmv, C0, C2, C4, B0, hCp, hCmv, hC0, hC2, hC4,
      hB0, hPowered⟩ :=
    finite_source_arbitrary_power_outputs_fully_uniform_native
      epsilon eta P hepsilon heta
  obtain ⟨Uscale, hUscale, hScale⟩ :=
    eventually_heathBrown_selected_scale_two hdelta1 hdelta2 hdeltaOrder
      hdelta1Upper
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  let U0 := max B0 (max Uscale Ucut)
  refine ⟨C, Cp, Cmv, C0, C2, C4, B0, U0, hC, hCp, hCmv, hC0,
    hC2, hC4, hB0, ?_, ?_⟩
  · exact hUscale.trans
      ((le_max_left Uscale Ucut).trans (le_max_right B0 (max Uscale Ucut)))
  · intro U hU d label hW hSquare
    have hB0U : B0 ≤ U := (le_max_left _ _).trans hU
    have hRest : max Uscale Ucut ≤ U := (le_max_right _ _).trans hU
    have hUscale' : Uscale ≤ U := (le_max_left _ _).trans hRest
    have hUcut' : Ucut ≤ U := (le_max_right _ _).trans hRest
    have hCutData := hCut U hUcut'
    dsimp only at hCutData
    have hX : 0 < Nat.floor (U ^ (delta2 / 2)) := hCutData.1
    have hY : 0 < Nat.floor (U ^ delta1) := by omega
    have hUOne : 1 ≤ U := by linarith [hUscale.trans hUscale']
    have hUPos : 0 < U := zero_lt_one.trans_le hUOne
    have hq0 : 0 < U ^ (-delta2) := Real.rpow_pos_of_pos hUPos _
    have hData := classicalBinarySourceSelectedFamily_alternative d label
      hY hX hq0 hC heta.le hsigma
      (fun n hn => hCoeffBound _ _ n hn) hW
    dsimp only at hData
    have hScaleData := hScale U hUscale' label.1 hSquare
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
    let R := 2 * U + U ^ delta
    have hpTwo : 2 ≤ p := by
      simpa only [N, p] using hScaleData.2.2.1
    have hp : 0 < p := by omega
    have hpP0 : p ≤ Nat.ceil (4 / delta2) := by
      simpa only [N, p] using hScaleData.2.2.2.2.2.2
    have hpP : p ≤ P := by
      dsimp only [P, heathBrownLongPowerCap]
      omega
    have hPowDelta : U ^ delta ≤ U := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
    have hThreeP : 3 ≤ P := by
      dsimp only [P, heathBrownLongPowerCap]
      omega
    have hTwoPow : (8 : Real) ≤ (2 : Real) ^ P := by
      have hNat : 2 ^ 3 ≤ 2 ^ P := Nat.pow_le_pow_right (by omega) hThreeP
      exact_mod_cast hNat
    have hRB : 2 * R ≤ (2 ^ P : Real) * U := by
      dsimp only [R]
      calc
        2 * (2 * U + U ^ delta) ≤ 8 * U := by nlinarith
        _ ≤ (2 : Real) ^ P * U :=
          mul_le_mul_of_nonneg_right hTwoPow hUPos.le
    have hL : 0 < L := by
      have hkIProduct : 0 < d.kI * 2 := d.hkI
      have hkIIProduct : 0 < d.kII * 2 := d.hkII
      have hkI : 0 < d.kI := by omega
      have hkII : 0 < d.kII := by omega
      dsimp only [L]
      exact classicalBinarySelectedThreshold_pos hY hX hkI hkII hq0 hC label.1
    have hAmbientCutoff : B0 ≤ (2 ^ P : Real) * U := by
      have hOnePow : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
      calc
        B0 ≤ U := hB0U
        _ = 1 * U := by ring
        _ ≤ (2 : Real) ^ P * U :=
          mul_le_mul_of_nonneg_right hOnePow hUPos.le
    have hOutputs := hPowered U R L N p
      (classicalBinaryColorFamily d label) a hUOne
      (by simpa only [N] using hData.1) hp hpP hRB
      (by simpa only [N, p] using hScaleData.2.2.2.1) hL
      (classicalBinaryColorFamily_separated d label)
      (classicalBinaryColorFamily_in_symmetric_shell d label)
      hData.2.1 hData.2.2.1 hAmbientCutoff
    refine ⟨⟨hData.1, hData.2.1, hData.2.2.1, hSquare, ?_, ?_⟩⟩
    · simpa only [N, p] using
        ⟨hScaleData.2.2.1, hScaleData.2.2.2.1,
          hScaleData.2.2.2.2.1, hScaleData.2.2.2.2.2.1, hpP0⟩
    · simpa only [N, a, L, p, P, R] using hOutputs

#print axioms heathBrownLongPowerCap
#print axioms HeathBrownFullyUniformLongSourceColorOutput
#print axioms eventually_heathBrownFullyUniformLongSourceColorOutput

end

end GafniTao
