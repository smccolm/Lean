import GafniTao.ClassicalBinarySignedShell
import GafniTao.EnergyDetectorSharpShellLocal
import GafniTao.EnergyDetectorShellCardinality

/-!
# Energy-preserving classical detector on a signed zero shell

This module composes the actual pointwise classical Type-I/Type-II detector
with the four-coordinate binary extractor.  Each coordinate of a resonant
zero quadruple may independently select its branch, dyadic scale, and source
sign.  No branch is selected by a one-dimensional cardinality pigeonhole.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Decode a signed Type-I scale. -/
def classicalTypeIShellScalePair {k : Nat} (q : Fin (k * 2)) :
    Fin k × Fin 2 :=
  finProdFinEquiv.symm q

/-- Physical length of a signed Type-I dyadic block. -/
def classicalTypeIShellScaleN {k : Nat} (Y : Nat) (q : Fin (k * 2)) : Nat :=
  2 ^ (classicalTypeIShellScalePair q).1.val * Y

/-- Coefficients of a signed Type-I dyadic block. -/
noncomputable def classicalTypeIShellScaleCoeff
    (A : Nat) (sigma : Real) {k : Nat} (q : Fin (k * 2)) : Nat → Complex :=
  signedClassicalLongCoeff A sigma (classicalTypeIShellScalePair q).2

/-- Literal Type-I large-value predicate delivered by the detector. -/
def ClassicalTypeIShellScaleLarge
    (A Y k : Nat) (sigma q0 : Real) (q : Fin (k * 2)) (t : Real) : Prop :=
  ((3 / 4) * (q0 / 2)) / k ≤
    ‖sourceDirichletPoly (classicalTypeIShellScaleN Y q)
      (classicalTypeIShellScaleCoeff A sigma q) t‖

/-- Decode a signed Type-II scale. -/
def classicalTypeIIShellScalePair {k : Nat} (q : Fin (k * 2)) :
    Fin k × Fin 2 :=
  finProdFinEquiv.symm q

/-- Source sign carried by either branch of a binary shell-scale label. -/
def classicalBinaryShellScaleSign
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)) : Fin 2 :=
  Sum.elim (fun r => (classicalTypeIShellScalePair r).2)
    (fun r => (classicalTypeIIShellScalePair r).2) (binaryScaleLabel q)

/-- Physical length of a signed Type-II dyadic block. -/
def classicalTypeIIShellScaleN {k : Nat} (X : Nat) (q : Fin (k * 2)) : Nat :=
  2 ^ (classicalTypeIIShellScalePair q).1.val * X

/-- Coefficients of a signed Type-II dyadic block. -/
noncomputable def classicalTypeIIShellScaleCoeff
    (Y X : Nat) (sigma : Real) {k : Nat} (q : Fin (k * 2)) : Nat → Complex :=
  signedSharpMollifiedLineCoeff Y X sigma
    (classicalTypeIIShellScalePair q).2

/-- Literal Type-II large-value predicate delivered by the detector. -/
def ClassicalTypeIIShellScaleLarge
    (Y X k : Nat) (sigma : Real) (q : Fin (k * 2)) (t : Real) : Prop :=
  ((3 / 4) * (3 / 4)) / k ≤
    ‖sourceDirichletPoly (classicalTypeIIShellScaleN X q)
      (classicalTypeIIShellScaleCoeff Y X sigma q) t‖

private theorem exp_two_le_eight_binary : Real.exp 2 ≤ 8 := by
  rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- Exact binary energy extraction on the actual multiplicity-weighted signed
dyadic zero shell.  The resulting `label i` retains the branch in
`binaryScaleLabel`, the source sign in the corresponding product label, and
the parity color in its second component. -/
theorem absoluteSlab_classical_binary_energy_extraction
    (sigma delta B₁ D₁ B₂ D₂ : Real)
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) :
    ∃ T₀ : Real, 8 ≤ T₀ ∧
      ∀ (U : Real) (Y X : Nat), T₀ ≤ U →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff U⌋₊ →
        (∀ rho ∈ zerosInRect sigma 1 U (2 * U),
          149 * sharpZetaCutoff U ^ (-rho.re) ≤ U ^ (-D₁) / 2) →
        U ^ (-D₁) * (X : Real) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff U⌋₊) (fun _n => 1) ≤ U ^ B₁ →
        U ^ (-D₁ - 1) ≤ U ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ U ^ B₂ →
        U ^ (-D₂) ≤ 3 / 4 →
        let A := ⌊sharpZetaCutoff U⌋₊
        let q0 := U ^ (-D₁)
        let kI := Nat.clog 2 A
        let kII := Nat.clog 2 Y
        let H := U ^ delta
        0 < kI * 2 ∧ 0 < kII * 2 ∧
        ∃ label : Fin 4 → (Fin (kI * 2 + kII * 2) × Fin 2),
          ∃ W : Fin 4 → Finset Real,
          (∀ i : Fin 4, IsSeparated 1 (W i)) ∧
          (∀ i : Fin 4, ∀ t, t ∈ W i →
            Sum.elim
              (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
              (ClassicalTypeIIShellScaleLarge Y X kII sigma)
              (binaryScaleLabel (label i).1) t) ∧
          (∀ i : Fin 4, ∀ t, t ∈ W i →
            -(2 * U + H) ≤ t ∧ t ≤ 2 * U + H) ∧
          (∀ i : Fin 4, (W i).card ≤ zeroCount sigma (2 * U)) ∧
          weightedAdditiveEnergyOn
              (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 ≤
            (2 * (kI * 2 + kII * 2)) ^ 4 *
                ((2 * ⌈H + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U) ^ 4 *
              MixedApproxAddEnergy (1 + 4 * (H + 1))
                (W 0) (W 1) (W 2) (W 3) := by
  obtain ⟨T₀, hT₀, hWitness⟩ :=
    absoluteSlab_classical_binary_pointwise_witness
      sigma delta B₁ D₁ B₂ D₂ hsigma hsigmaUpper hdelta
  refine ⟨T₀, hT₀, ?_⟩
  intro U Y X hU hX hY hXY hYA hError hShort hMassI hThresholdI
    hMassII hThresholdII
  let A := ⌊sharpZetaCutoff U⌋₊
  let q0 := U ^ (-D₁)
  let kI := Nat.clog 2 A
  let kII := Nat.clog 2 Y
  let H := U ^ delta
  obtain ⟨hkI, hkII, hEach⟩ := hWitness U Y X hU hX hY hXY hYA
    hError hShort hMassI hThresholdI hMassII hThresholdII
  let largeI : Fin (kI * 2) → Real → Prop :=
    ClassicalTypeIShellScaleLarge A Y kI sigma q0
  let largeII : Fin (kII * 2) → Real → Prop :=
    ClassicalTypeIIShellScaleLarge Y X kII sigma
  let inInterval : Real → Prop := fun t =>
    -(2 * U + H) ≤ t ∧ t ≤ 2 * U + H
  have hEachI : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      ∀ hb : signedChoosesClassicalTypeI Y q0 rho,
        ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
          ∃ r : Fin (kI * 2), largeI r t := by
    intro rho hrho hb
    obtain ⟨t, ht, htI, r, _hrOriented, hr⟩ := (hEach rho hrho).1 hb
    refine ⟨t, ht, htI, r, ?_⟩
    simpa [largeI, ClassicalTypeIShellScaleLarge,
      classicalTypeIShellScaleN, classicalTypeIShellScaleCoeff,
      classicalTypeIShellScalePair] using hr
  have hEachII : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      ∀ hb : ¬ signedChoosesClassicalTypeI Y q0 rho,
        ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
          ∃ r : Fin (kII * 2), largeII r t := by
    intro rho hrho hb
    obtain ⟨t, ht, htI, r, _hrOriented, hr⟩ := (hEach rho hrho).2 hb
    refine ⟨t, ht, htI, r, ?_⟩
    simpa [largeII, ClassicalTypeIIShellScaleLarge,
      classicalTypeIIShellScaleN, classicalTypeIIShellScaleCoeff,
      classicalTypeIIShellScalePair] using hr
  have hLocalHeight : max (Real.exp 2) 8 ≤ 2 * U := by
    apply max_le
    · exact exp_two_le_eight_binary.trans (by linarith [hT₀.trans hU])
    · linarith [hT₀.trans hU]
  have hLocal : ∀ z : Int,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun y => (z : Real) ≤ y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) ≤ sharpShellLocalMultiplicityCap U := by
    intro z
    exact absoluteDyadicZeroSlab_unitBin_multiplicity_le sigma U z
      (by linarith) hLocalHeight
  obtain ⟨label, W, hSep, hLarge, hInterval, hCard, hEnergy⟩ :=
    finite_binary_shifted_energy_extraction_on
      (absoluteDyadicZeroSlab sigma U) zeroMultiplicity 1 H
      (kI * 2) (kII * 2) (sharpShellLocalMultiplicityCap U) hkI
      largeI largeII (signedChoosesClassicalTypeI Y q0) inInterval
      hEachI hEachII hLocal
  refine ⟨hkI, hkII, label, W, hSep, ?_, ?_, ?_, hEnergy⟩
  · simpa only [largeI, largeII, A, q0, kI, kII] using hLarge
  · simpa only [inInterval, H] using hInterval
  · intro i
    exact (hCard i).trans
      (absoluteDyadicZeroSlab_card_le_zeroCount sigma U
        (by linarith [hT₀.trans hU]))

#print axioms absoluteSlab_classical_binary_energy_extraction

end

end GafniTao
