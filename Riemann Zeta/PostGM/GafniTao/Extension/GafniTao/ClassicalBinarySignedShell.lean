import GafniTao.ClassicalBinaryPointwise
import GafniTao.EnergyDetectorSharpSlab

/-!
# Signed-shell form of the classical binary detector

This module transports the pointwise Type-I/Type-II alternative from the
positive height slab to the actual signed dyadic shell used by the
multiplicity-weighted four-zero energy.  The sign is part of each finite
scale label and the resulting polynomials use the positive-sign source
convention.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The branch predicate on a signed shell. -/
def signedChoosesClassicalTypeI
    (Y : Nat) (q : Real) (rho : Complex) : Prop :=
  if rho.im < 0 then ChoosesClassicalTypeI Y q (star rho)
  else ChoosesClassicalTypeI Y q rho

/-- Source-convention Type-I coefficients for the two signs. -/
noncomputable def signedClassicalLongCoeff
    (A : Nat) (sigma : Real) (sign : Fin 2) (n : Nat) : Complex :=
  if sign = 0 then conjugateCoeffs (classicalZetaLongLineCoeff A sigma) n
  else classicalZetaLongLineCoeff A sigma n

/-- Source-convention Type-II coefficients for the two signs. -/
noncomputable def signedSharpMollifiedLineCoeff
    (Y X : Nat) (sigma : Real) (sign : Fin 2) (n : Nat) : Complex :=
  if sign = 0 then conjugateCoeffs (sharpMollifiedLineCoeff Y X sigma) n
  else sharpMollifiedLineCoeff Y X sigma n

/-- Exact signed-shell binary detector.  The two scale spaces have sizes
`kI*2` and `kII*2`; decoding with `finProdFinEquiv.symm` exposes the dyadic
index and source sign. -/
theorem absoluteSlab_classical_binary_pointwise_witness
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
        let q := U ^ (-D₁)
        let kI := Nat.clog 2 A
        let kII := Nat.clog 2 Y
        0 < kI * 2 ∧ 0 < kII * 2 ∧
        ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
          (signedChoosesClassicalTypeI Y q rho →
            ∃ t : Real, |rho.im - t| ≤ U ^ delta ∧
              (-(2 * U + U ^ delta) ≤ t ∧
                t ≤ 2 * U + U ^ delta) ∧
              ∃ label : Fin (kI * 2),
                let rsign := finProdFinEquiv.symm label
                (if rsign.2 = 0 then U - U ^ delta ≤ t
                  else t ≤ -(U - U ^ delta)) ∧
                  ((3 / 4) * (q / 2)) / kI ≤
                    ‖sourceDirichletPoly (2 ^ rsign.1.val * Y)
                      (signedClassicalLongCoeff A sigma rsign.2) t‖ ∧
                  (3 / 4) * (q / 2) ≤
                    ‖classicalZetaLongTail Y A
                      ((sigma : Complex) +
                        Complex.I *
                          (((if rsign.2 = 0 then t else -t) : Real) :
                            Complex))‖) ∧
          (¬ signedChoosesClassicalTypeI Y q rho →
            ∃ t : Real, |rho.im - t| ≤ U ^ delta ∧
              (-(2 * U + U ^ delta) ≤ t ∧
                t ≤ 2 * U + U ^ delta) ∧
              ∃ label : Fin (kII * 2),
                let rsign := finProdFinEquiv.symm label
                (if rsign.2 = 0 then U - U ^ delta ≤ t
                  else t ≤ -(U - U ^ delta)) ∧
                  ((3 / 4) * (3 / 4)) / kII ≤
                    ‖sourceDirichletPoly (2 ^ rsign.1.val * X)
                      (signedSharpMollifiedLineCoeff Y X sigma rsign.2) t‖) := by
  obtain ⟨T₀, hT₀, hPositive⟩ :=
    positiveSlab_classical_binary_pointwise_witness
      sigma delta B₁ D₁ B₂ D₂ hsigma hsigmaUpper hdelta
  refine ⟨T₀, hT₀, ?_⟩
  intro U Y X hU hX hY hXY hYA hError hShort hMassI hThresholdI
    hMassII hThresholdII
  have hUPos : 0 < U := by linarith [hT₀.trans hU]
  have hRaw := hPositive U Y X hU hX hY hXY hYA hError hShort
    hMassI hThresholdI hMassII hThresholdII
  dsimp only at hRaw ⊢
  let A := ⌊sharpZetaCutoff U⌋₊
  let q := U ^ (-D₁)
  let kI := Nat.clog 2 A
  let kII := Nat.clog 2 Y
  obtain ⟨hkI, hkII, hEach⟩ := hRaw
  refine ⟨Nat.mul_pos hkI (by norm_num), Nat.mul_pos hkII (by norm_num), ?_⟩
  intro rho hrho
  rw [absoluteDyadicZeroSlab, Finset.mem_union] at hrho
  rcases hrho with hneg | hpos
  · have hrhoNeg : rho.im < 0 := by
      have hRect := hneg
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hRect
      linarith
    have hconj := conj_mem_positiveSlab_of_mem_negativeSlab hneg
    have hPosData := hEach (star rho) hconj
    constructor
    · intro hChoice
      have hChoiceConj : ChoosesClassicalTypeI Y q (star rho) := by
        simpa [signedChoosesClassicalTypeI, hrhoNeg] using hChoice
      obtain ⟨s, hsShift, hsInterval, r, hrLarge, hrTail⟩ :=
        hPosData.1 hChoiceConj
      let label : Fin (kI * 2) := finProdFinEquiv (r, (1 : Fin 2))
      refine ⟨-s, ?_, ?_, label, ?_, ?_, ?_⟩
      · calc
          |rho.im - -s| = |-rho.im - s| := by
            rw [← abs_neg]
            congr 1
            ring
          _ = |(star rho).im - s| := by simp
          _ ≤ U ^ delta := hsShift
      · constructor <;> linarith [hsInterval.1, hsInterval.2]
      · have hsOriented : -s ≤ -(U - U ^ delta) := by
          linarith [hsInterval.1]
        simpa [label] using hsOriented
      · simpa [label, signedClassicalLongCoeff,
          ← dirichletPoly_neg_eq_sourceDirichletPoly] using hrLarge
      · simpa [label] using hrTail
    · intro hChoice
      have hChoiceConj : ¬ ChoosesClassicalTypeI Y q (star rho) := by
        simpa [signedChoosesClassicalTypeI, hrhoNeg] using hChoice
      obtain ⟨s, hsShift, hsInterval, r, hrLarge⟩ :=
        hPosData.2 hChoiceConj
      let label : Fin (kII * 2) := finProdFinEquiv (r, (1 : Fin 2))
      refine ⟨-s, ?_, ?_, label, ?_, ?_⟩
      · calc
          |rho.im - -s| = |-rho.im - s| := by
            rw [← abs_neg]
            congr 1
            ring
          _ = |(star rho).im - s| := by simp
          _ ≤ U ^ delta := hsShift
      · constructor <;> linarith [hsInterval.1, hsInterval.2]
      · have hsOriented : -s ≤ -(U - U ^ delta) := by
          linarith [hsInterval.1]
        simpa [label] using hsOriented
      · simpa [label, signedSharpMollifiedLineCoeff,
          ← dirichletPoly_neg_eq_sourceDirichletPoly] using hrLarge
  · have hRect := hpos
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hRect
    have hrhoNonneg : ¬ rho.im < 0 := by linarith
    have hPosData := hEach rho hpos
    constructor
    · intro hChoice
      have hChoicePos : ChoosesClassicalTypeI Y q rho := by
        simpa [signedChoosesClassicalTypeI, hrhoNonneg] using hChoice
      obtain ⟨t, htShift, htInterval, r, hrLarge, hrTail⟩ :=
        hPosData.1 hChoicePos
      let label : Fin (kI * 2) := finProdFinEquiv (r, (0 : Fin 2))
      refine ⟨t, htShift, ?_, label, ?_, ?_, ?_⟩
      · constructor <;> linarith [htInterval.1, htInterval.2]
      · simpa [label] using htInterval.1
      · simp only [label, Equiv.symm_apply_apply]
        change ((3 / 4) * (q / 2)) / kI ≤
          ‖sourceDirichletPoly (2 ^ r.val * Y)
            (signedClassicalLongCoeff A sigma 0) t‖
        rw [show signedClassicalLongCoeff A sigma 0 =
            conjugateCoeffs (classicalZetaLongLineCoeff A sigma) from by
          funext n
          simp [signedClassicalLongCoeff]]
        simpa only [norm_sourceDirichletPoly_conjugateCoeffs] using hrLarge
      · simpa [label] using hrTail
    · intro hChoice
      have hChoicePos : ¬ ChoosesClassicalTypeI Y q rho := by
        simpa [signedChoosesClassicalTypeI, hrhoNonneg] using hChoice
      obtain ⟨t, htShift, htInterval, r, hrLarge⟩ :=
        hPosData.2 hChoicePos
      let label : Fin (kII * 2) := finProdFinEquiv (r, (0 : Fin 2))
      refine ⟨t, htShift, ?_, label, ?_, ?_⟩
      · constructor <;> linarith [htInterval.1, htInterval.2]
      · simpa [label] using htInterval.1
      · simp only [label, Equiv.symm_apply_apply]
        change ((3 / 4) * (3 / 4)) / kII ≤
          ‖sourceDirichletPoly (2 ^ r.val * X)
            (signedSharpMollifiedLineCoeff Y X sigma 0) t‖
        rw [show signedSharpMollifiedLineCoeff Y X sigma 0 =
            conjugateCoeffs (sharpMollifiedLineCoeff Y X sigma) from by
          funext n
          simp [signedSharpMollifiedLineCoeff]]
        simpa only [norm_sourceDirichletPoly_conjugateCoeffs] using hrLarge

#print axioms absoluteSlab_classical_binary_pointwise_witness

end

end GafniTao
