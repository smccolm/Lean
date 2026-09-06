import GafniTao.ClassicalBinaryUniformSourceAlternative
import GafniTao.HeathBrownFullyUniformOutputs

/-!
# Fully uniform source-cutoff Heath--Brown alternative

All analytic constants in this version are selected before the physical
height.  In particular, the mollified-coefficient constant, the Type-I MHH
constant, the finite-power constant, and the mean-value constant cannot vary
with a detector colour or height.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

set_option maxHeartbeats 800000

/-- Source output for one actual detector colour with every analytic constant
fixed by the enclosing eventual theorem. -/
structure HeathBrownFullyUniformSourceColorOutput
    (sigma U delta delta1 delta2 eta epsilon : Real)
    (K C Cp Cmv C0 C2 C4 : Real)
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
  direct : ∀ r : Fin (d.kI * 2),
    binaryScaleLabel label.1 = Sum.inl r →
    let N := classicalBinarySelectedN
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    Nonempty (HeathBrownFullyUniformOutputs epsilon
      ((2 ^ P : Real) * (6 * U)) R N 1 eta L
      (classicalBinaryColorFamily d label) a Cp Cmv C0 C2 C4)
  /-- The same globally selected constants apply to every powered dyadic
  subblock extracted from this Type-I source family.  This field is what
  permits lower-edge source blocks to be powered after energy-safe dyadic
  extraction, without reselecting constants inside a zero quadruple. -/
  powered :
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    ∀ (N p : Nat) (L : Real) (W : Finset Real) (a : Nat -> Complex),
      0 < N -> 0 < p -> p <= P ->
      (N : Real) ^ p <= U -> 0 < L ->
      IsSeparated 1 W ->
      (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
      (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
      (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
      Nonempty (HeathBrownFullyUniformOutputs epsilon
        ((2 ^ P : Real) * U) R N p eta L W a
        Cp Cmv C0 C2 C4)
  /-- Constant-factor enlargement for the exact dyadic transition
  `N^p <= 4U`.  The factor four is retained in the ambient parameter and is
  absorbed only by the later physical exponent transfer. -/
  scaled :
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    ∀ (N p : Nat) (L : Real) (W : Finset Real) (a : Nat -> Complex),
      0 < N -> 0 < p -> p <= P ->
      (N : Real) ^ p <= 4 * U -> 0 < L ->
      IsSeparated 1 W ->
      (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
      (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
      (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
      Nonempty (HeathBrownFullyUniformOutputs epsilon
        ((2 ^ P : Real) * (4 * U)) R N p eta L W a
        Cp Cmv C0 C2 C4)
  /-- A one-power packet at the original wide ambient height.  It handles
  the exact source edge whose extracted dyadic length is comparable with
  (and may be slightly larger than) the physical height. -/
  wide :
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    ∀ (N : Nat) (L : Real) (W : Finset Real) (a : Nat -> Complex),
      0 < N -> (N : Real) <= 6 * U -> 0 < L ->
      IsSeparated 1 W ->
      (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
      (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
      (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
      Nonempty (HeathBrownFullyUniformOutputs epsilon
        ((2 ^ P : Real) * (6 * U)) R N 1 eta L W a
        Cp Cmv C0 C2 C4)
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
    ∃ r : Fin (d.kII * 2),
      binaryScaleLabel label.1 = Sum.inr r ∧
      Nonempty (HeathBrownFullyUniformOutputs epsilon
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a Cp Cmv C0 C2 C4)

/-- Every nonempty source detector colour eventually has either the exact
Type-I output or fully uniform consecutive-power outputs.  All constants are
chosen before `U`, the detector, and the colour. -/
theorem eventually_heathBrownFullyUniformSourceColorOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ K C Cp Cmv C0 C2 C4 B0 U0 : Real,
      0 < K ∧ 0 < C ∧ 1 ≤ Cp ∧ 0 < Cmv ∧
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧ 8 ≤ U0 ∧
      ∀ U : Real, U0 ≤ U →
        ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
          (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2),
          (classicalBinaryColorFamily d label).Nonempty →
          Nonempty (HeathBrownFullyUniformSourceColorOutput sigma U delta
            delta1 delta2 eta epsilon K C Cp Cmv C0 C2 C4 d label) := by
  obtain ⟨K, hK, hMHH⟩ := classicalBinaryColorFamily_typeI_mhh_native
  obtain ⟨C, hC, hCoeffBound⟩ := sharpMollifiedCoeff_bound eta heta
  let P := Nat.ceil (4 / delta2)
  obtain ⟨Cp, Cmv, C0, C2, C4, B0, hCp, hCmv, hC0, hC2, hC4,
      hB0, hPowered⟩ :=
    finite_source_arbitrary_power_outputs_fully_uniform_native
      epsilon eta P hepsilon heta
  obtain ⟨Uscale, hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  obtain ⟨Ushift, hUshift, hShift⟩ :=
    eventually_rpow_le_half_self hdeltaUpper
  let U0 := max B0 (max Uscale (max Ucut Ushift))
  refine ⟨K, C, Cp, Cmv, C0, C2, C4, B0, U0, hK, hC, hCp,
    hCmv, hC0, hC2, hC4, hB0, ?_, ?_⟩
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
    have hData := classicalBinarySourceSelectedFamily_alternative d label
      hY hX hq0 hC heta.le hsigma
      (fun n hn => hCoeffBound _ _ n hn) hW
    dsimp only at hData
    let N := classicalBinarySelectedN
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
    let R := 2 * U + U ^ delta
    have hDirect : ∀ r : Fin (d.kI * 2),
        binaryScaleLabel label.1 = Sum.inl r →
        Nonempty (HeathBrownFullyUniformOutputs epsilon
          ((2 ^ P : Real) * (6 * U)) R N 1 eta L
          (classicalBinaryColorFamily d label) a Cp Cmv C0 C2 C4) := by
      intro r hrLabel
      have hNA : N < Nat.floor (sharpZetaCutoff U) := by
        rcases hData.2.2.2 with hTypeI | hTypeII
        · obtain ⟨rI, hrILabel, _hrLower, hrUpper⟩ := hTypeI
          have hrEq : rI = r := by
            rw [hrLabel] at hrILabel
            exact Sum.inl_injective hrILabel.symm
          subst rI
          simpa only [N, classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
            hrUpper
        · obtain ⟨rII, hrIILabel, _hrLower, _hrUpper⟩ := hTypeII
          rw [hrLabel] at hrIILabel
          have hne : (Sum.inl r : Sum (Fin (d.kI * 2)) (Fin (d.kII * 2))) ≠
              Sum.inr rII := by simp
          exact False.elim (hne hrIILabel)
      have hNU : (N : Real) ≤ 6 * U := by
        have hCutNonneg : 0 ≤ sharpZetaCutoff U := by
          have hFour := four_mul_lt_sharpZetaCutoff U
          nlinarith
        have hFloor : (Nat.floor (sharpZetaCutoff U) : Real) ≤
            sharpZetaCutoff U := by exact_mod_cast Nat.floor_le hCutNonneg
        have hNFloor : (N : Real) ≤
            (Nat.floor (sharpZetaCutoff U) : Real) := by exact_mod_cast hNA.le
        exact hNFloor.trans (hFloor.trans
          (sharpZetaCutoff_le_six_mul (by linarith)))
      have hPOne : 1 ≤ P := by
        exact Nat.one_le_ceil_iff.mpr (by positivity : 0 < 4 / delta2)
      have hPowDelta : U ^ delta ≤ U := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
      have hRBDirect : 2 * R ≤ (2 ^ P : Real) * (6 * U) := by
        have hOnePow : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
        dsimp only [R]
        calc
          2 * (2 * U + U ^ delta) ≤ 6 * U := by nlinarith
          _ = 1 * (6 * U) := by ring
          _ ≤ (2 : Real) ^ P * (6 * U) := by
            gcongr
      have hL : 0 < L := by
        have hkI : 0 < d.kI := by have := d.hkI; omega
        have hkII : 0 < d.kII := by have := d.hkII; omega
        dsimp only [L]
        exact classicalBinarySelectedThreshold_pos hY hX hkI hkII hq0 hC label.1
      have hAmbientDirect : B0 ≤ (2 ^ P : Real) * (6 * U) := by
        have hOnePow : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
        calc
          B0 ≤ U := hB0U
          _ ≤ 6 * U := by nlinarith
          _ = 1 * (6 * U) := by ring
          _ ≤ (2 : Real) ^ P * (6 * U) := by gcongr
      exact hPowered (6 * U) R L N 1
        (classicalBinaryColorFamily d label) a
        (by nlinarith) (by simpa only [N] using hData.1) (by omega) hPOne
        hRBDirect (by simpa using hNU)
        hL (classicalBinaryColorFamily_separated d label)
        (classicalBinaryColorFamily_in_symmetric_shell d label)
        (by simpa only [a] using hData.2.1)
        (by simpa only [N, a, L] using hData.2.2.1) hAmbientDirect
    have hPoweredAll : ∀ (N p : Nat) (L : Real) (W : Finset Real)
        (a : Nat -> Complex),
        0 < N -> 0 < p -> p <= P ->
        (N : Real) ^ p <= U -> 0 < L ->
        IsSeparated 1 W ->
        (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
        (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
        (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
        Nonempty (HeathBrownFullyUniformOutputs epsilon
          ((2 ^ P : Real) * U) R N p eta L W a
          Cp Cmv C0 C2 C4) := by
      intro N' p' L' W' a' hN' hp' hpP' hPower' hL' hSep' hSymm'
        hCoeff' hLarge'
      have hPowDelta : U ^ delta <= U := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
      have hdelta2Upper : delta2 <= 2 / 3 := by
        nlinarith [hCube]
      have hThreeReal : (3 : Real) <= 4 / delta2 := by
        rw [le_div_iff₀ hdelta2]
        nlinarith
      have hPThree : 3 <= P := by
        exact_mod_cast hThreeReal.trans (Nat.le_ceil (4 / delta2))
      have hTwoPow : (8 : Real) <= (2 : Real) ^ P := by
        exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hPThree
      have hRBAll : 2 * R <= (2 ^ P : Real) * U := by
        dsimp only [R]
        calc
          2 * (2 * U + U ^ delta) <= 8 * U := by nlinarith
          _ <= (2 : Real) ^ P * U :=
            mul_le_mul_of_nonneg_right hTwoPow hUPos.le
      have hAmbientAll : B0 <= (2 ^ P : Real) * U := by
        have hOnePow : (1 : Real) <= (2 : Real) ^ P :=
          one_le_pow₀ (by norm_num)
        calc
          B0 <= U := hB0U
          _ = 1 * U := by ring
          _ <= (2 : Real) ^ P * U := by gcongr
      exact hPowered U R L' N' p' W' a'
        hUOne hN' hp' hpP' hRBAll hPower' hL' hSep' hSymm'
        hCoeff' hLarge' hAmbientAll
    have hWide : ∀ (N : Nat) (L : Real) (W : Finset Real)
        (a : Nat -> Complex),
        0 < N -> (N : Real) <= 6 * U -> 0 < L ->
        IsSeparated 1 W ->
        (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
        (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
        (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
        Nonempty (HeathBrownFullyUniformOutputs epsilon
          ((2 ^ P : Real) * (6 * U)) R N 1 eta L W a
          Cp Cmv C0 C2 C4) := by
      intro N' L' W' a' hN' hNU hL' hSep' hSymm' hCoeff' hLarge'
      have hPowDelta : U ^ delta <= U := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
      have hPOne : 1 <= P := by
        exact Nat.one_le_ceil_iff.mpr (by positivity : 0 < 4 / delta2)
      have hRBWide : 2 * R <= (2 ^ P : Real) * (6 * U) := by
        have hOnePow : (1 : Real) <= (2 : Real) ^ P :=
          one_le_pow₀ (by norm_num)
        dsimp only [R]
        calc
          2 * (2 * U + U ^ delta) <= 6 * U := by nlinarith
          _ = 1 * (6 * U) := by ring
          _ <= (2 : Real) ^ P * (6 * U) := by gcongr
      have hAmbientWide : B0 <= (2 ^ P : Real) * (6 * U) := by
        have hOnePow : (1 : Real) <= (2 : Real) ^ P :=
          one_le_pow₀ (by norm_num)
        calc
          B0 <= U := hB0U
          _ <= 6 * U := by nlinarith
          _ = 1 * (6 * U) := by ring
          _ <= (2 : Real) ^ P * (6 * U) := by gcongr
      exact hPowered (6 * U) R L' N' 1 W' a'
        (by nlinarith) hN' (by omega) hPOne hRBWide
        (by simpa using hNU) hL' hSep' hSymm' hCoeff' hLarge' hAmbientWide
    have hScaled : ∀ (N p : Nat) (L : Real) (W : Finset Real)
        (a : Nat -> Complex),
        0 < N -> 0 < p -> p <= P ->
        (N : Real) ^ p <= 4 * U -> 0 < L ->
        IsSeparated 1 W ->
        (∀ t, t ∈ W -> -R <= t ∧ t <= R) ->
        (∀ n ∈ dyadicInterval N, ‖a n‖ <= 1) ->
        (∀ t ∈ W, L <= ‖sourceDirichletPoly N a t‖) ->
        Nonempty (HeathBrownFullyUniformOutputs epsilon
          ((2 ^ P : Real) * (4 * U)) R N p eta L W a
          Cp Cmv C0 C2 C4) := by
      intro N' p' L' W' a' hN' hp' hpP' hPower' hL' hSep' hSymm'
        hCoeff' hLarge'
      have hPowDelta : U ^ delta <= U := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hUOne hdeltaUpper.le
      have hPOne : 1 <= P := by
        exact Nat.one_le_ceil_iff.mpr (by positivity : 0 < 4 / delta2)
      have hRBScaled : 2 * R <= (2 ^ P : Real) * (4 * U) := by
        have hOnePow : (1 : Real) <= (2 : Real) ^ P :=
          one_le_pow₀ (by norm_num)
        dsimp only [R]
        calc
          2 * (2 * U + U ^ delta) <= 6 * U := by nlinarith
          _ <= 4 * (2 * U) := by nlinarith
          _ <= (2 : Real) ^ P * (4 * U) := by
            have hTwoPow : (2 : Real) <= (2 : Real) ^ P := by
              exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
                hPOne
            nlinarith
      have hAmbientScaled : B0 <= (2 ^ P : Real) * (4 * U) := by
        have hOnePow : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
        calc
          B0 <= U := hB0U
          _ <= 4 * U := by nlinarith
          _ = 1 * (4 * U) := by ring
          _ <= (2 : Real) ^ P * (4 * U) := by gcongr
      exact hPowered (4 * U) R L' N' p' W' a'
        (by nlinarith) hN' hp' hpP' hRBScaled hPower' hL' hSep' hSymm'
        hCoeff' hLarge' hAmbientScaled
    refine ⟨⟨hData.1, hData.2.1, hData.2.2.1,
      by simpa only [N, a, L, P, R] using hDirect,
      by simpa only [P, R] using hPoweredAll,
      by simpa only [P, R] using hScaled,
      by simpa only [P, R] using hWide, ?_⟩⟩
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
      have hOutputs := hPowered U R
        (classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1)
        N p (classicalBinaryColorFamily d label)
        (classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1)
        hUOne (by simpa only [N] using hData.1) hp hpP hRB
        (by simpa only [N, p] using hScaleData.2.2.2.2.2.1)
        hL (classicalBinaryColorFamily_separated d label)
        (classicalBinaryColorFamily_in_symmetric_shell d label)
        hData.2.1 hData.2.2.1 hAmbientCutoff
      exact ⟨r, hrLabel, by simpa only [N, p, P, R] using hOutputs⟩

#print axioms HeathBrownFullyUniformSourceColorOutput
#print axioms eventually_heathBrownFullyUniformSourceColorOutput

end

end GafniTao
