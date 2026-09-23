import TaoTrudgianYang2025.ClassicalTypeISourceClasses
import TaoTrudgianYang2025.ClassicalTypeIICardinalityTransfer
import TaoTrudgianYang2025.ClassicalSlabCardinalityClasses
import TaoTrudgianYang2025.ClassicalSlabCardinalityLoss

/-!
# Actual multiplicity-weighted zero-slab cardinality transfer

All cutoffs and threshold windows are chosen in source order. The two
large-value predicates are genuine upstream inputs; neither a zero count
nor an equivalent detector-family count is assumed.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalSlabZeroCount_bound_of_uniform_largeValue_bounds
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueBound σ τ (B * τ))
    (hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ 1 / 2 < σ - δ ∧
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ T : ℝ in Filter.atTop,
          (zeroCountRect (σ - δ) 1 T (2 * T) : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  let a : ℝ := min (1 / 2) (1 / (4 * τ₀))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have haHalf : a ≤ 1 / 2 := min_le_left _ _
  have haSmall : a ≤ 1 / (4 * τ₀) := min_le_right _ _
  have hτa : τ₀ ≤ 1 / (2 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    have hx := (le_div_iff₀ (by positivity : 0 < 4 * τ₀)).mp haSmall
    nlinarith
  obtain ⟨CI, hCI, δI, hδI, hI⟩ :=
    classicalTypeI_uniform_source_class_cardinality_bound σ B a hB ha (by linarith)
      (fun τ hτ => hZeta τ hτ.1) (ε / 2) (by linarith)
  let D : ℝ := min (a * δI / 16) (min a (1 / 4))
  have hD : 0 < D := lt_min (by positivity) (lt_min ha (by norm_num))
  have hDsmall : D ≤ a * δI / 16 := min_le_left _ _
  have hDa : D ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hDquarter : D ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let b := D / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b ≤ a := by dsimp [b]; linarith
  have hτab : τ₀ ≤ 1 / (a + b) :=
    hτa.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  obtain ⟨CII, hCII, δII, hδII, hII⟩ :=
    classicalTypeII_uniform_source_class_cardinality_bound σ B a b hB ha hb hba
      (by linarith) (fun τ hτ => hGeneral τ (hτab.trans hτ.1))
      (ε / 2) (by linarith)
  let δ := min ((σ - 1 / 2) / 2) (min (δI / 4) (δII / 4))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδσ : δ ≤ (σ - 1 / 2) / 2 := min_le_left _ _
  have hδIle : δ ≤ δI / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδIIle : δ ≤ δII / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let s := σ - δ
  have hs : 1 / 2 < s := by dsimp [s]; linarith
  have hsUpper : s ≤ 1 := by dsimp [s]; linarith
  obtain ⟨θ, hθ, hθone, hθε, hIbound⟩ := hI s D (by linarith)
    (by dsimp [s]; linarith) (by linarith) (by linarith)
  have hIIbound := hII s D θ (by linarith) (by dsimp [s]; linarith) hθone.le
  obtain ⟨K, hK, hloss⟩ := eventually_classicalSlabCardinalityLoss_le_const_mul_rpow θ hθ
  obtain ⟨Tbranch, hTbranch, hbranch⟩ :=
    classicalSlab_exists_all_separated_cardinality_classes
      s θ 2 D 4 1 hs hsUpper hθ
  obtain ⟨Tcut, hTcut, hcut⟩ := eventually_classical_dichotomy_cutoffs
    a D ha hD (by dsimp [b] at hba; exact hba) (by linarith)
  obtain ⟨Tproduct, _hTproduct, hproduct⟩ := eventually_classical_short_product_le_quarter D hD
  obtain ⟨Terror, _hTerror, herror⟩ :=
    eventually_sharp_full_error_le_split_threshold s D (by linarith) (by linarith)
  let C : ℝ := max 1 (K * max CI CII)
  refine ⟨δ, hδ, hs, C, le_max_left _ _, ?_⟩
  filter_upwards [hIbound, hIIbound, hloss,
    Filter.eventually_ge_atTop Tbranch, Filter.eventually_ge_atTop Tcut,
    Filter.eventually_ge_atTop Tproduct, Filter.eventually_ge_atTop Terror] with
      T hIbound hIIbound hloss hTB hTC hTP hTE
  have hT : 8 ≤ T := hTbranch.trans hTB
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  let Y := ⌊T ^ a⌋₊
  let X := ⌊T ^ b⌋₊
  let L := (2 * Nat.ceil (T ^ θ) + 1) * classicalLocalMultiplicityCap T
  have hcut' := hcut T hTC
  dsimp only at hcut'
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds T D Y X hT
      hcut'.2.2.2.2.2 hcut'.2.2.2.2.1
  obtain ⟨shiftedZero, baseColor, hlocal, _hshift, hinterval,
    hlarge, _hsep, _hcount⟩ :=
    hbranch T Y X hTB hcut'.1 hcut'.2.1 hcut'.2.2.1 hcut'.2.2.2.1
      (herror T hTE) (hproduct T hTP) hMassI hThresholdI hMassII hThresholdII
  let color := classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal
  have hclass (c : ClassicalSeparatedBranchScaleColor T Y L) :
      (Fintype.card (EnergyColorFiber color c) : ℝ) ≤
        max CI CII * T ^ (B + ε / 2) := by
    cases hlabel : c.1 with
    | none =>
      haveI : IsEmpty (EnergyColorFiber color c) := ⟨fun x => by
        have hx := hlarge c x
        change ClassicalBranchScaleLarge s T D Y X c.1 (shiftedZero x.1.1) at hx
        simp only [hlabel, ClassicalBranchScaleLarge] at hx⟩
      rw [Fintype.card_of_isEmpty, Nat.cast_zero]
      exact mul_nonneg (zero_le_one.trans (hCI.trans (le_max_left _ _)))
        (Real.rpow_nonneg hTpos.le _)
    | some branch =>
      cases branch with
      | inl r =>
        exact (hIbound X L shiftedZero baseColor hlocal c r hlabel
          hinterval (hlarge c)).trans (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (Real.rpow_nonneg hTpos.le _))
      | inr r =>
        exact (hIIbound L shiftedZero baseColor hlocal c r hlabel
          hinterval (hlarge c)).trans (mul_le_mul_of_nonneg_right
            (le_max_right _ _) (Real.rpow_nonneg hTpos.le _))
  have hslab : (zeroCountRect s 1 T (2 * T) : ℝ) ≤
      classicalSlabCardinalityLoss T θ Y * (max CI CII * T ^ (B + ε / 2)) := by
    rw [← classicalSlabZeroCopy_card]
    exact cardinality_le_color_count_mul color (max CI CII * T ^ (B + ε / 2)) hclass
  have hMaxNonneg : 0 ≤ max CI CII := zero_le_one.trans (hCI.trans (le_max_left _ _))
  calc
    (zeroCountRect (σ - δ) 1 T (2 * T) : ℝ) ≤
        classicalSlabCardinalityLoss T θ Y * (max CI CII * T ^ (B + ε / 2)) := hslab
    _ ≤ (K * T ^ (3 * θ)) * (max CI CII * T ^ (B + ε / 2)) :=
      mul_le_mul_of_nonneg_right (hloss Y hcut'.2.2.2.1) (by positivity)
    _ = (K * max CI CII) * T ^ (3 * θ + (B + ε / 2)) := by
      rw [Real.rpow_add hTpos (3 * θ) (B + ε / 2)]
      ring
    _ ≤ C * T ^ (B + ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTone (by linarith))
        (Real.rpow_nonneg hTpos.le _) (zero_le_one.trans (le_max_left _ _))


end TaoTrudgianYang2025
