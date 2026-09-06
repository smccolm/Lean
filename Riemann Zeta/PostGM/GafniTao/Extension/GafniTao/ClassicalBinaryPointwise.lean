import GafniTao.BinaryEnergyExtraction
import RiemannZeta.GuthMaynard.ClassicalDichotomy

/-!
# Pointwise classical Type-I/Type-II zero detector

The frozen classical dichotomy finishes by selecting one branch according to
weighted cardinality.  That final selection cannot be used for four-zero
energy.  This module stops one step earlier and exposes the genuine
pointwise alternative, so a later four-coordinate coloring may choose Type I
or Type II independently in each coordinate.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The pointwise detector underlying the frozen classical dichotomy.  All
finite mass and threshold hypotheses are still explicit; a later physical
scale module discharges them uniformly. -/
theorem positiveSlab_classical_binary_pointwise_witness
    (sigma delta B₁ D₁ B₂ D₂ : Real)
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) :
    ∃ T₀ : Real, 8 ≤ T₀ ∧
      ∀ (T : Real) (Y X : Nat), T₀ ≤ T →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
        (∀ rho ∈ zerosInRect sigma 1 T (2 * T),
          149 * sharpZetaCutoff T ^ (-rho.re) ≤ T ^ (-D₁) / 2) →
        T ^ (-D₁) * (X : Real) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
        T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
        T ^ (-D₂) ≤ 3 / 4 →
        let A := ⌊sharpZetaCutoff T⌋₊
        let q := T ^ (-D₁)
        let kI := Nat.clog 2 A
        let kII := Nat.clog 2 Y
        0 < kI ∧ 0 < kII ∧
        ∀ rho, rho ∈ zerosInRect sigma 1 T (2 * T) →
          (ChoosesClassicalTypeI Y q rho →
            ∃ t : Real, |rho.im - t| ≤ T ^ delta ∧
              (T - T ^ delta ≤ t ∧ t ≤ 2 * T + T ^ delta) ∧
              ∃ r : Fin kI,
                ((3 / 4) * (q / 2)) / kI ≤
                  ‖dirichletPoly (2 ^ r.val * Y)
                    (classicalZetaLongLineCoeff A sigma) t‖ ∧
                (3 / 4) * (q / 2) ≤
                  ‖classicalZetaLongTail Y A
                    ((sigma : Complex) + Complex.I * (t : Complex))‖) ∧
          (¬ ChoosesClassicalTypeI Y q rho →
            ∃ t : Real, |rho.im - t| ≤ T ^ delta ∧
              (T - T ^ delta ≤ t ∧ t ≤ 2 * T + T ^ delta) ∧
              ∃ r : Fin kII,
                ((3 / 4) * (3 / 4)) / kII ≤
                  ‖dirichletPoly (2 ^ r.val * X)
                    (sharpMollifiedLineCoeff Y X sigma) t‖) := by
  obtain ⟨T₁, hT₁, hBetaI⟩ :=
    finiteDirichlet_beta_removal_power_threshold delta hdelta B₁ (D₁ + 1)
  obtain ⟨T₂, hT₂, hBetaII⟩ :=
    finiteDirichlet_beta_removal_power_threshold delta hdelta B₂ D₂
  let T₀ := max T₁ T₂
  refine ⟨T₀, hT₁.trans (le_max_left _ _), ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
    hThresholdI hMassII hThresholdII
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let q := T ^ (-D₁)
  let kI := Nat.clog 2 A
  let kII := Nat.clog 2 Y
  have hT₁' : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT₂' : T₂ ≤ T := (le_max_right _ _).trans hT
  have hTEight : 8 ≤ T := hT₁.trans hT₁'
  have hTpos : 0 < T := by linarith
  have hqPos : 0 < q := Real.rpow_pos_of_pos hTpos _
  have hA : 1 < A := by
    have hCutNonneg : 0 ≤ sharpZetaCutoff T :=
      (four_mul_lt_sharpZetaCutoff T).le.trans'
        (mul_nonneg (by norm_num) hTpos.le)
    have hTwo : (2 : Real) ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T]
    have hTwoNat : 2 ≤ A := (Nat.le_floor_iff hCutNonneg).mpr hTwo
    omega
  have hY : 1 ≤ Y := hX.trans hXY
  have hkI : 0 < kI := Nat.clog_pos Nat.one_lt_two hA
  have hkII : 0 < kII := Nat.clog_pos Nat.one_lt_two hYStrict
  refine ⟨hkI, hkII, ?_⟩
  intro rho hrho
  have hRect := hrho
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  constructor
  · intro hChoice
    have hSharp : ‖classicalZetaPartialSum A rho‖ ≤ q / 2 := by
      have hBase := norm_zeta_zero_sharp_cutoff_sum_le
        (by linarith) hrho (by linarith : 0 < sigma)
      have hBase' : ‖classicalZetaPartialSum A rho‖ ≤
          149 * sharpZetaCutoff T ^ (-rho.re) := by
        simpa only [A, classicalZetaPartialSum] using hBase
      have hError' : 149 * sharpZetaCutoff T ^ (-rho.re) ≤ q / 2 := by
        simpa only [q] using hError rho hrho
      exact hBase'.trans hError'
    have hLong : q / 2 ≤ ‖classicalZetaLongTail Y A rho‖ := by
      have hRaw := classical_typeI_of_short_sum_large A Y rho (q / 2) q
        (by simpa only [A] using hYA) hSharp hChoice
      convert hRaw using 1
      ring
    obtain ⟨t, htShift, htLarge⟩ := hBetaI sigma T rho
      (classicalZetaLongTailSupport Y A) (fun _n => 1) (q / 2)
      hsigma.le hsigmaUpper hT₁' hRect.1.1 hRect.1.2.1
      (classicalZetaLongTailSupport_pos Y A)
      (by simpa only [A] using hMassI)
      (by simpa only [q, neg_add] using hThresholdI)
      (by simpa only [classicalZetaLongTail_eq_finiteDirichletSeries]
        using hLong)
    have htInterval : T - T ^ delta ≤ t ∧ t ≤ 2 * T + T ^ delta := by
      rw [abs_le] at htShift
      constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
    have htLarge' : (3 / 4) * (q / 2) ≤
        ‖classicalZetaLongTail Y A
          ((sigma : Complex) + Complex.I * (t : Complex))‖ := by
      simpa only [classicalZetaLongTail_eq_finiteDirichletSeries] using htLarge
    obtain ⟨r, hr, hrLarge⟩ := exists_classicalZetaLong_large_dyadic_block
      Y A sigma t ((3 / 4) * (q / 2)) hY hA htLarge'
    let rf : Fin kI := ⟨r, by simpa only [kI] using Finset.mem_range.mp hr⟩
    refine ⟨t, by simpa [abs_sub_comm] using htShift, htInterval, rf, ?_,
      htLarge'⟩
    simpa only [rf, kI] using hrLarge
  · intro hChoice
    have hShort : ‖classicalZetaPartialSum Y rho‖ ≤ q :=
      (lt_of_not_ge hChoice).le
    have hTailRaw := classical_typeII_of_short_sum_small Y X rho q (X : Real)
      hY hX hXY hqPos.le hShort
      (norm_zetaMollifier_le_length X rho (by linarith [hRect.1.1]))
    have hTail : 3 / 4 ≤ ‖sharpMollifiedTail Y X rho‖ := by
      linarith [hTailRaw, hShortProduct]
    obtain ⟨t, htShift, htLarge⟩ := hBetaII sigma T rho
      (sharpMollifiedTailSupport Y X) (sharpMollifiedCoeff Y X) (3 / 4)
      hsigma.le hsigmaUpper hT₂' hRect.1.1 hRect.1.2.1
      (sharpMollifiedTailSupport_pos Y X) hMassII hThresholdII
      (by simpa only [sharpMollifiedTail] using hTail)
    have htInterval : T - T ^ delta ≤ t ∧ t ≤ 2 * T + T ^ delta := by
      rw [abs_le] at htShift
      constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
    have htLarge' : (3 / 4) * (3 / 4) ≤
        ‖sharpMollifiedTail Y X
          ((sigma : Complex) + Complex.I * (t : Complex))‖ := by
      simpa only [sharpMollifiedTail] using htLarge
    obtain ⟨r, hr, hrLarge⟩ := exists_sharpMollified_large_dyadic_block
      Y X sigma t ((3 / 4) * (3 / 4)) hYStrict htLarge'
    let rf : Fin kII := ⟨r, by simpa only [kII] using Finset.mem_range.mp hr⟩
    refine ⟨t, by simpa [abs_sub_comm] using htShift, htInterval, rf, ?_⟩
    simpa only [rf, kII] using hrLarge

#print axioms positiveSlab_classical_binary_pointwise_witness

end

end GafniTao
