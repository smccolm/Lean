import TaoTrudgianYang2025.ClassicalPatternCardinality

/-!
# Complete multiplicity-safe cardinality extraction from a positive zero slab

The actual shifted detector branch/scale is refined by every separation
color, not a selected energy witness. The total analytic zero count is the
exact sum of the cardinalities of those fibers.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard
open scoped BigOperators

theorem classicalSlab_exists_all_separated_cardinality_classes
    (σ δ B₁ D₁ B₂ D₂ : ℝ)
    (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y X : ℕ), T₀ ≤ T →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
        (∀ ρ ∈ zerosInRect σ 1 T (2 * T),
          149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-D₁) / 2) →
        T ^ (-D₁) * (X : ℝ) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
        T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
        T ^ (-D₂) ≤ 3 / 4 →
        let L := (2 * Nat.ceil (T ^ δ) + 1) *
          classicalLocalMultiplicityCap T
        ∃ (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
          (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
            ClassicalBranchScaleColor T Y)
          (hlocal : ∀ z : ℤ,
            (unitBinFinset
              (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L),
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            |(ρ : ℂ).im - shiftedZero ρ| ≤ T ^ δ) ∧
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            T - T ^ δ ≤ shiftedZero ρ ∧
            shiftedZero ρ ≤ 2 * T + T ^ δ) ∧
          (let shifted := fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1
           let color := classicalSeparatedBranchScaleColor σ T Y
             shiftedZero baseColor L hlocal
           (∀ (c : ClassicalSeparatedBranchScaleColor T Y L)
               (x : EnergyColorFiber color c),
              ClassicalBranchScaleLarge σ T D₁ Y X c.1 (shifted x.1)) ∧
           (∀ (c : ClassicalSeparatedBranchScaleColor T Y L)
               (x y : EnergyColorFiber color c),
              x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) ∧
           zeroCountRect σ 1 T (2 * T) =
             ∑ c : ClassicalSeparatedBranchScaleColor T Y L,
               Fintype.card (EnergyColorFiber color c)) := by
  obtain ⟨T₀, hT₀, hSelect⟩ :=
    classicalSlab_exists_shifted_branch_scale σ δ B₁ D₁ B₂ D₂
      hσ hσUpper hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
    hThresholdI hMassII hThresholdII
  obtain ⟨shiftedZero, baseColor, hshiftZero, hinterval, hlargeZero⟩ :=
    hSelect T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
      hThresholdI hMassII hThresholdII
  let shifted : ClassicalSlabZeroCopy σ T → ℝ := fun x => shiftedZero x.1
  let base : ClassicalSlabZeroCopy σ T → ClassicalBranchScaleColor T Y :=
    fun x => baseColor x.1
  let L := (2 * Nat.ceil (T ^ δ) + 1) * classicalLocalMultiplicityCap T
  have hTEight : 8 ≤ T := hT₀.trans hT
  have hunit : ∀ z : ℤ,
      ∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤
          classicalLocalMultiplicityCap T := by
    intro z
    simpa only [zeroUnitBin] using
      zeroUnitBin_multiplicity_le_cap σ T z hσ.le hTEight
  have hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L := by
    intro z
    exact classicalSlabZeroCopy_shifted_unitBin_card_le σ T (T ^ δ)
      (classicalLocalMultiplicityCap T) shiftedZero hshiftZero hunit z
  refine ⟨shiftedZero, baseColor, hlocal, hshiftZero, hinterval, ?_, ?_, ?_⟩
  · intro c x
    have hcolor : baseColor x.1.1 = c.1 :=
      separatedRefinementColor_base shifted base L hlocal x.2
    rw [← hcolor]
    exact hlargeZero x.1.1
  · intro c x y hxy
    exact separatedRefinementColor_oneSeparated shifted base L hlocal c x y hxy
  · rw [← classicalSlabZeroCopy_card]
    exact cardinality_eq_sum_color_fibers
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)


end TaoTrudgianYang2025
