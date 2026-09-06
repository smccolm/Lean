import GafniTao.EnergyDetectorShellCardinality
import GafniTao.RealEnergyDiscretization

/-!
# Exact detector extraction on one signed dyadic zero shell

This module composes the actual signed sharp-mollifier witness with the
arbitrary weighted-subfamily extractor.  The source dyadic block and source
sign are encoded by `finProdFinEquiv`; the additional `Fin 2` in the output is
the parity color used to make each representative set one-separated.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Decode a single finite scale index into its exact dyadic-block and source-
sign labels. -/
def sharpShellScalePair {k : Nat} (q : Fin (k * 2)) : Fin k × Fin 2 :=
  finProdFinEquiv.symm q

/-- The physical Dirichlet-polynomial length at a signed shell scale. -/
def sharpShellScaleN {k : Nat} (X : Nat) (q : Fin (k * 2)) : Nat :=
  2 ^ ((sharpShellScalePair q).1 : Nat) * X

/-- The exact unit-normalized coefficient sequence at a signed shell scale. -/
noncomputable def sharpShellScaleCoeff
    (A X : Nat) (sigma eta C : Real) {k : Nat} (q : Fin (k * 2)) :
    Nat → Complex :=
  signedNormalizedSharpCoeff A X (fun _ => sharpShellScaleN X q)
    sigma eta C (sharpShellScalePair q).2

/-- The complete large-value predicate furnished by the signed shell
detector, including the unit coefficient bound and its literal threshold. -/
def SharpShellScaleLarge
    (A X k : Nat) (sigma eta C : Real) (q : Fin (k * 2)) (t : Real) : Prop :=
  (∀ n, n ∈ dyadicInterval (sharpShellScaleN X q) →
      ‖sharpShellScaleCoeff A X sigma eta C q n‖ ≤ 1) ∧
    ((3 / 8) / (k : Real)) /
          (C * (2 * sharpShellScaleN X q : Real) ^ eta *
            (sharpShellScaleN X q : Real) ^ (-sigma)) ≤
      ‖sourceDirichletPoly (sharpShellScaleN X q)
        (sharpShellScaleCoeff A X sigma eta C q) t‖

private theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- Full finite energy extraction for the actual multiplicity-weighted signed
dyadic zero shell.  All color, displacement, local-multiplicity, and
mixed-to-self defect-window losses remain explicit. -/
theorem absoluteSlab_sharpMollified_energy_extraction
    (sigma delta eta : Real) (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma ≤ 1) (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ C T0 : Real, 0 < C ∧
      (∀ (A X n : Nat), 0 < n →
        ‖sharpMollifiedCoeff A X n‖ ≤ C * (n : Real) ^ eta) ∧
      8 ≤ T0 ∧
      ∀ (U : Real) (X : Nat), T0 ≤ U →
        1 ≤ X → X ≤ ⌊sharpZetaCutoff U⌋₊ → (X : Real) ≤ U →
        let A := ⌊sharpZetaCutoff U⌋₊
        let k := Nat.clog 2 A
        let H := U ^ delta
        0 < k ∧
        ∃ label : Fin 4 → (Fin (k * 2) × Fin 2),
          ∃ W : Fin 4 → Finset Real,
          (∀ i : Fin 4, IsSeparated 1 (W i)) ∧
          (∀ i : Fin 4, ∀ t, t ∈ W i →
            SharpShellScaleLarge A X k sigma eta C (label i).1 t) ∧
          (∀ i : Fin 4, ∀ t, t ∈ W i →
            -(2 * U + H) ≤ t ∧ t ≤ 2 * U + H) ∧
          (∀ i : Fin 4, (W i).card ≤ zeroCount sigma (2 * U)) ∧
          4 * (weightedAdditiveEnergyOn
              (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) ≤
            (((2 * (k * 2)) ^ 4 *
                ((2 * ⌈H + 1⌉₊ + 1) *
                  sharpShellLocalMultiplicityCap U) ^ 4 : Nat) : Real) *
              (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
                ((ApproxAddEnergy 1 (W 0) : Real) +
                  (ApproxAddEnergy 1 (W 1) : Real) +
                  (ApproxAddEnergy 1 (W 2) : Real) +
                  (ApproxAddEnergy 1 (W 3) : Real)) := by
  obtain ⟨C, T0, hC, hCoeff, hT0, hWitness⟩ :=
    absoluteSlab_sharpMollified_energy_witness sigma delta eta
      hsigma hsigmaUpper hdelta heta
  refine ⟨C, T0, hC, hCoeff, hT0, ?_⟩
  intro U X hU hX hXA hXU
  let A := ⌊sharpZetaCutoff U⌋₊
  let k := Nat.clog 2 A
  let H := U ^ delta
  obtain ⟨hk, hEachRaw⟩ := hWitness U X hU hX hXA hXU
  have hK : 0 < k * 2 := Nat.mul_pos hk (by norm_num)
  let large : Fin (k * 2) → Real → Prop :=
    SharpShellScaleLarge A X k sigma eta C
  let inInterval : Real → Prop := fun t =>
    -(2 * U + H) ≤ t ∧ t ≤ 2 * U + H
  have hEach : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
        ∃ q : Fin (k * 2), large q t := by
    intro rho hrho
    obtain ⟨t, ht, htI, r, hrCoeff, hrLarge⟩ := hEachRaw rho hrho
    let q : Fin (k * 2) := finProdFinEquiv r
    refine ⟨t, ht, htI, q, ?_⟩
    constructor
    · intro n hn
      have hn' : n ∈ dyadicInterval
          ((fun _sign : Fin 2 => 2 ^ (r.1 : Nat) * X) r.2) := by
        simpa [sharpShellScaleN, sharpShellScalePair, q] using hn
      simpa [large, SharpShellScaleLarge, sharpShellScaleCoeff,
        sharpShellScaleN, sharpShellScalePair, q] using hrCoeff n hn'
    · simpa [large, SharpShellScaleLarge, sharpShellScaleCoeff,
        sharpShellScaleN, sharpShellScalePair, q] using hrLarge
  have hLocalHeight : max (Real.exp 2) 8 ≤ 2 * U := by
    apply max_le
    · exact exp_two_le_eight.trans (by linarith [hT0.trans hU])
    · linarith [hT0.trans hU]
  have hLocal : ∀ z : Int,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun y => (z : Real) ≤ y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) ≤ sharpShellLocalMultiplicityCap U := by
    intro z
    exact absoluteDyadicZeroSlab_unitBin_multiplicity_le sigma U z
      (by linarith) hLocalHeight
  obtain ⟨label, hSep, hLarge, hInterval, hEnergy⟩ :=
    finite_shifted_dyadic_energy_extraction_on
      (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 H
      (k * 2) (sharpShellLocalMultiplicityCap U) hK large inInterval
      hEach hLocal
  let shift : Complex → Real := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (hEach rho h)
    else rho.im
  let scale : Complex → Fin (k * 2) := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hK⟩
  let representative :=
    detectorRepresentative (absoluteDyadicZeroSlab sigma U) scale shift
  let W := fun i : Fin 4 =>
    ((absoluteDyadicZeroSlab sigma U).filter
      (fun rho => detectorColor scale shift rho = label i)).image representative
  refine ⟨hk, label, W, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, representative, scale, shift] using hSep
  · simpa only [large, A, k, W, representative, scale, shift] using hLarge
  · simpa only [inInterval, H, W, representative, scale, shift] using hInterval
  · intro i
    exact image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U (by linarith [hT0.trans hU]) _ _
  let P : Nat := (2 * (k * 2)) ^ 4 *
    ((2 * ⌈H + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U) ^ 4
  let M : Nat := MixedApproxAddEnergy (1 + 4 * (H + 1))
    (W 0) (W 1) (W 2) (W 3)
  let S : Real :=
    (ApproxAddEnergy 1 (W 0) : Real) +
      (ApproxAddEnergy 1 (W 1) : Real) +
      (ApproxAddEnergy 1 (W 2) : Real) +
      (ApproxAddEnergy 1 (W 3) : Real)
  have hEnergyReal :
      (weightedAdditiveEnergyOn (absoluteDyadicZeroSlab sigma U)
          zeroMultiplicity 1 : Real) ≤ (P : Real) * (M : Real) := by
    exact_mod_cast hEnergy
  have hMixed : 4 * (M : Real) ≤
      (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S := by
    simpa only [M, S] using
      four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
        (by simpa only [W, representative, scale, shift] using hSep 0)
        (by simpa only [W, representative, scale, shift] using hSep 1)
        (by simpa only [W, representative, scale, shift] using hSep 2)
        (by simpa only [W, representative, scale, shift] using hSep 3)
  change 4 * (weightedAdditiveEnergyOn
      (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) ≤
    (P : Real) *
      (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S
  calc
    4 * (weightedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 : Real) ≤
        4 * ((P : Real) * (M : Real)) := by gcongr
    _ = (P : Real) * (4 * (M : Real)) := by ring
    _ ≤ (P : Real) *
        ((doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S) := by
      gcongr
    _ = (P : Real) *
        (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S := by ring

#print axioms sharpShellScalePair
#print axioms sharpShellScaleN
#print axioms sharpShellScaleCoeff
#print axioms absoluteSlab_sharpMollified_energy_extraction

end

end GafniTao
