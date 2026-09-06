import GafniTao.EnergyDetectorPoweredFamily

/-!
# The signed sharp zero shell consumed by powered Guth--Maynard energy

This module composes the actual multiplicity-weighted shell extraction with
positive-sign powering, exact translation, two stages of four-coordinate
coloring, and the frozen Proposition 11.1.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact finite source-entry theorem for one signed dyadic zero shell. The
detector chooses its four source blocks before the caller chooses the four
powering degrees and analytic heights. The only remaining premises are the
displayed physical scale and powered-threshold comparisons. -/
theorem absoluteSlab_powered_gm_energy_bound
    (sigma delta etaDetector : Real)
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) (hetaDetector : 0 < etaDetector) :
    ∃ Cdet T0 : Real, 0 < Cdet ∧ 8 ≤ T0 ∧
      ∀ (U : Real) (X : Nat), T0 ≤ U →
        1 ≤ X → X ≤ ⌊sharpZetaCutoff U⌋₊ → (X : Real) ≤ U →
        let A := ⌊sharpZetaCutoff U⌋₊
        let k := Nat.clog 2 A
        let H := U ^ delta
        let R := 2 * U + H
        ∃ outerLabel : Fin 4 → (Fin (k * 2) × Fin 2),
          ∃ W : Fin 4 → Finset Real,
          let N := fun i : Fin 4 => sharpShellScaleN X (outerLabel i).1
          let a := fun i : Fin 4 =>
            sharpShellScaleCoeff A X sigma etaDetector Cdet
              (outerLabel i).1
          let L := fun i : Fin 4 =>
            ((3 / 8) / (k : Real)) /
              (Cdet * (2 * N i : Real) ^ etaDetector *
                (N i : Real) ^ (-sigma))
          (∀ i : Fin 4, (W i).card ≤ zeroCount sigma (2 * U)) ∧
          ∀ (B : Fin 4 → Real) (p : Fin 4 → Nat)
              (etaPower epsilon : Real),
            (∀ i, 0 < p i) → (∀ i, 2 * R ≤ B i) →
            0 < etaPower → 0 < epsilon →
            ∃ Cp Cgm B0 : Fin 4 → Real,
              (∀ i, 0 < Cp i) ∧ (∀ i, 0 < Cgm i) ∧
              (∀ i, 4 ≤ B0 i) ∧
              ((∀ i, B0 i ≤ B i) →
                (∀ i r, r ∈ Finset.range (p i) →
                  (2 ^ r * (N i) ^ (p i) : Real) ≤ B i) →
                (∀ i r, r ∈ Finset.range (p i) →
                  (B i) ^ (3 / 4 : Real) ≤
                    (2 ^ r * (N i) ^ (p i) : Real)) →
                (∀ i r, r ∈ Finset.range (p i) →
                  (2 ^ r * (N i) ^ (p i) : Real) ^ sigma ≤
                    ((L i) ^ (p i) /
                      (Cp i *
                        ((2 ^ (p i) * (N i) ^ (p i) : Nat) : Real) ^
                          etaPower)) /
                      (p i)) →
                ∃ label : (i : Fin 4) → Fin 4 → Fin (p i),
                  ∃ V : Fin 4 → Fin 4 → Finset Real,
                  (∀ i : Fin 4,
                    (∀ j : Fin 4, V i j ⊆ gmTranslate R (W i)) ∧
                    (∀ j : Fin 4,
                      (V i j).card ≤ zeroCount sigma (2 * U)) ∧
                    (∀ j : Fin 4, IsSeparated 1 (V i j)) ∧
                    (∀ j : Fin 4, InBaseInterval (B i) (V i j)) ∧
                    (∀ j : Fin 4, ∀ n ∈ dyadicInterval
                        (2 ^ (label i j).val * (N i) ^ (p i)),
                      ‖sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                        (phaseShiftCoeffs R (a i)) (Cp i) etaPower n‖ ≤ 1) ∧
                    (∀ j : Fin 4, ∀ t ∈ V i j,
                      (2 ^ (label i j).val * (N i) ^ (p i) : Real) ^ sigma ≤
                        ‖sourceDirichletPoly
                          (2 ^ (label i j).val * (N i) ^ (p i))
                          (sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                            (phaseShiftCoeffs R (a i)) (Cp i) etaPower) t‖)) ∧
                  16 * (weightedAdditiveEnergyOn
                      (absoluteDyadicZeroSlab sigma U)
                      zeroMultiplicity 1 : Real) ≤
                    (((2 * (k * 2)) ^ 4 *
                        ((2 * ⌈H + 1⌉₊ + 1) *
                          sharpShellLocalMultiplicityCap U) ^ 4 : Nat) : Real) *
                      (doubleFloorDefectWindow
                        (1 + 4 * (H + 1))).card *
                      ∑ i : Fin 4,
                        ((((p i) ^ 4 : Nat) : Real) *
                          (doubleFloorDefectWindow 1).card *
                          (Cgm i * (B i) ^ epsilon *
                            ∑ j : Fin 4,
                              gmEnergyShape sigma (B i)
                                (2 ^ (label i j).val *
                                  (N i) ^ (p i))
                                (V i j)))) := by
  obtain ⟨Cdet, T0, hCdet, hCoeffDet, hT0, hShell⟩ :=
    absoluteSlab_sharpMollified_energy_extraction
      sigma delta etaDetector hsigma hsigmaUpper hdelta hetaDetector
  refine ⟨Cdet, T0, hCdet, hT0, ?_⟩
  intro U X hU hX hXA hXU
  dsimp only
  let A := ⌊sharpZetaCutoff U⌋₊
  let k := Nat.clog 2 A
  let H := U ^ delta
  let R := 2 * U + H
  obtain ⟨hk, outerLabel, W, hSep, hScaleLarge, hSymm, hWcard,
      hOuterEnergy⟩ :=
    hShell U X hU hX hXA hXU
  let N := fun i : Fin 4 => sharpShellScaleN X (outerLabel i).1
  let a := fun i : Fin 4 =>
    sharpShellScaleCoeff A X sigma etaDetector Cdet (outerLabel i).1
  let L := fun i : Fin 4 =>
    ((3 / 8) / (k : Real)) /
      (Cdet * (2 * N i : Real) ^ etaDetector * (N i : Real) ^ (-sigma))
  have hN : ∀ i : Fin 4, 0 < N i := by
    intro i
    dsimp only [N, sharpShellScaleN]
    exact Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hL : ∀ i : Fin 4, 0 ≤ L i := by
    intro i
    have hNReal : (0 : Real) < N i := by exact_mod_cast hN i
    have hkReal : (0 : Real) < k := by exact_mod_cast hk
    dsimp only [L]
    positivity
  have hCoeff : ∀ i n, n ∈ dyadicInterval (N i) → ‖a i n‖ ≤ 1 := by
    intro i n hn
    have hNi : 0 < N i := hN i
    dsimp only [a, sharpShellScaleCoeff, signedNormalizedSharpCoeff]
    split_ifs with hsign
    · rw [norm_conjugateCoeffs]
      apply norm_normalizedSharpMollifiedLineCoeff_le_one
        _ _ _ _ _ _ _ hNi (by linarith) hetaDetector.le hCdet
          (fun m hm => hCoeffDet _ _ m hm) hn
    · apply norm_normalizedSharpMollifiedLineCoeff_le_one
        _ _ _ _ _ _ _ hNi (by linarith) hetaDetector.le hCdet
          (fun m hm => hCoeffDet _ _ m hm) hn
  have hLarge : ∀ i t, t ∈ W i →
      L i ≤ ‖sourceDirichletPoly (N i) (a i) t‖ := by
    intro i t ht
    simpa only [L, N, a] using (hScaleLarge i t ht).2
  have hSymm' : ∀ i t, t ∈ W i → -R ≤ t ∧ t ≤ R := by
    intro i t ht
    simpa only [R] using hSymm i t ht
  refine ⟨outerLabel, W, ?_, ?_⟩
  · exact hWcard
  dsimp only
  intro B p etaPower epsilon hp hRB hetaPower hepsilon
  obtain ⟨Cp, Cgm, B0, hCp, hCgm, hB0, hConsume⟩ :=
    finite_four_symmetric_source_powered_energy_gm_bound
      epsilon sigma R B p N a etaPower L W hepsilon hp hetaPower
      hN hL hSep hSymm' hRB hCoeff hLarge
  refine ⟨Cp, Cgm, B0, hCp, hCgm, hB0, ?_⟩
  intro hB hUpper hLower hThreshold
  obtain ⟨label, V, hInner⟩ := hConsume hB hUpper hLower hThreshold
  refine ⟨label, V, ?_, ?_⟩
  · intro i
    refine ⟨(hInner i).1, ?_, (hInner i).2.1, (hInner i).2.2.1,
      (hInner i).2.2.2.1, (hInner i).2.2.2.2.1⟩
    intro j
    calc
      (V i j).card ≤ (gmTranslate R (W i)).card :=
        Finset.card_le_card ((hInner i).1 j)
      _ = (W i).card := card_gmTranslate R (W i)
      _ ≤ zeroCount sigma (2 * U) := hWcard i
  ·
    have hInnerEnergy : ∀ i : Fin 4,
      4 * (ApproxAddEnergy 1 (W i) : Real) ≤
        (((p i) ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (Cgm i * (B i) ^ epsilon *
            ∑ j : Fin 4, gmEnergyShape sigma (B i)
              (2 ^ (label i j).val * (N i) ^ (p i)) (V i j)) := by
      intro i
      have hi := (hInner i).2.2.2.2.2
      simpa only [Fin.sum_univ_four] using hi
    let P : Real :=
      (((2 * (k * 2)) ^ 4 *
        ((2 * ⌈H + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U) ^ 4 : Nat) : Real)
    let D : Real :=
      (doubleFloorDefectWindow (1 + 4 * (H + 1))).card
    let S : Real := ∑ i : Fin 4, (ApproxAddEnergy 1 (W i) : Real)
    let Q : Fin 4 → Real := fun i =>
      (((p i) ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (Cgm i * (B i) ^ epsilon *
          ∑ j : Fin 4, gmEnergyShape sigma (B i)
            (2 ^ (label i j).val * (N i) ^ (p i)) (V i j))
    have hOuter : 4 * (weightedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) ≤
        P * D * S := by
      simpa only [A, k, H, P, D, S, Fin.sum_univ_four] using hOuterEnergy
    have hSum : 4 * S ≤ ∑ i : Fin 4, Q i := by
      calc
        4 * S = ∑ i : Fin 4, 4 * (ApproxAddEnergy 1 (W i) : Real) := by
          simp only [S, Finset.mul_sum]
        _ ≤ ∑ i : Fin 4, Q i := by
          exact Finset.sum_le_sum fun i _hi => hInnerEnergy i
    change 16 * (weightedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) ≤
      P * D * ∑ i : Fin 4, Q i
    calc
      16 * (weightedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) =
          4 * (4 * (weightedAdditiveEnergyOn
            (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real)) := by ring
      _ ≤ 4 * (P * D * S) :=
        mul_le_mul_of_nonneg_left hOuter (by norm_num)
      _ = P * D * (4 * S) := by ring
      _ ≤ P * D * ∑ i : Fin 4, Q i := by
        exact mul_le_mul_of_nonneg_left hSum (by
          dsimp only [P, D]
          positivity)

#print axioms absoluteSlab_powered_gm_energy_bound

end

end GafniTao
