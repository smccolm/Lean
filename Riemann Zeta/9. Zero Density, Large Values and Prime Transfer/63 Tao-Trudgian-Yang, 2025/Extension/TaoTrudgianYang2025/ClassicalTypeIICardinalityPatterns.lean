import TaoTrudgianYang2025.ClassicalPatternCardinality

/-!
# Cardinality-preserving actual Type-II source patterns

The original sharp mollifier and its proved divisor normalization are used.
The pattern ordinate count equals the full analytic-copy class cardinality.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_classicalTypeIIClassCardinalityPattern
    (δ σ T D₁ η C : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (label : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 Y))
    (hlabel : label.1 = some (Sum.inr r))
    (hT : 0 < T) (hY : 1 < Y)
    (hN : 1 < 2 ^ (r : ℕ) * X)
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hC : 0 < C)
    (hCoeff : ∀ m : ℕ, 0 < m →
      ‖sharpMollifiedCoeff Y X m‖ ≤ C * (m : ℝ) ^ η)
    (hinterval : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      T - T ^ δ ≤ shiftedZero ρ ∧
        shiftedZero ρ ≤ 2 * T + T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      ClassicalBranchScaleLarge σ T D₁ Y X label.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    ∃ P : LargeValuePattern,
      let N := 2 ^ (r : ℕ) * X
      let D := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
      P.N = (N : ℝ) ∧
      P.scale = N ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D ∧
      P.ordinates.card =
        Fintype.card (EnergyColorFiber
          (classicalSeparatedBranchScaleColor σ T Y
            shiftedZero baseColor L hlocal) label) := by
  let N := 2 ^ (r : ℕ) * X
  let D : ℝ := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
  let threshold : ℝ := (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D
  let W := fun x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label => shiftedZero x.1.1
  have hNpos : 0 < N := by omega
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hk : 0 < Nat.clog 2 Y := Nat.clog_pos Nat.one_lt_two hY
  have hkReal : (0 : ℝ) < Nat.clog 2 Y := by exact_mod_cast hk
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hcoeff : ∀ n ∈ dyadicInterval N,
      ‖normalizedSharpMollifiedLineCoeff Y X N σ η C n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one Y X N n σ η C
      hNpos hσ hη hC hCoeff hn
  have hW : ∀ x, T - T ^ δ ≤ W x ∧ W x ≤ 2 * T + T ^ δ := by
    intro x
    exact hinterval x.1.1
  have hsepW : ∀ x y, x ≠ y → 1 ≤ |W x - W y| := hsep
  have hraw : ∀ x, ((3 / 4) * (3 / 4)) / Nat.clog 2 Y ≤
      ‖dirichletPoly N (sharpMollifiedLineCoeff Y X σ) (W x)‖ := by
    intro x
    have hx := hlarge x
    rw [hlabel] at hx
    simpa only [ClassicalBranchScaleLarge, ClassicalTypeIILargeAt, N, W] using hx
  have hlargeNorm : ∀ x, threshold ≤
      ‖dirichletPoly N
        (normalizedSharpMollifiedLineCoeff Y X N σ η C) (W x)‖ := by
    intro x
    rw [dirichletPoly_normalizedSharpMollifiedLineCoeff, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hraw x) hD.le
  have hab : T - T ^ δ < 2 * T + T ^ δ := by
    have hpow : 0 ≤ T ^ δ := Real.rpow_nonneg hT.le δ
    linarith
  let P := indexedDirichletLargeValuePattern N threshold
    (T - T ^ δ) (2 * T + T ^ δ)
    (normalizedSharpMollifiedLineCoeff Y X N σ η C) W hN hthreshold hab
    hcoeff hW hsepW hlargeNorm
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact indexedDirichletLargeValuePattern_card N threshold
      (T - T ^ δ) (2 * T + T ^ δ)
      (normalizedSharpMollifiedLineCoeff Y X N σ η C) W hN hthreshold hab
      hcoeff hW hsepW hlargeNorm

/-- Native Type-II pattern packaging with the coefficient majorant discharged
by the proved uniform sharp-mollifier divisor bound. -/
theorem exists_classicalTypeIIClassCardinalityPattern_native
    (δ σ T D₁ η : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (label : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 Y))
    (hlabel : label.1 = some (Sum.inr r))
    (hT : 0 < T) (hY : 1 < Y)
    (hN : 1 < 2 ^ (r : ℕ) * X)
    (hσ : 0 ≤ σ) (hη : 0 < η)
    (hinterval : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      T - T ^ δ ≤ shiftedZero ρ ∧
        shiftedZero ρ ≤ 2 * T + T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      ClassicalBranchScaleLarge σ T D₁ Y X label.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : LargeValuePattern,
      let N := 2 ^ (r : ℕ) * X
      let D := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
      P.N = (N : ℝ) ∧
      P.scale = N ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D ∧
      P.ordinates.card =
        Fintype.card (EnergyColorFiber
          (classicalSeparatedBranchScaleColor σ T Y
            shiftedZero baseColor L hlocal) label) := by
  obtain ⟨C, hC, hCoeff⟩ := sharpMollifiedCoeff_bound η hη
  refine ⟨C, hC, ?_⟩
  exact exists_classicalTypeIIClassCardinalityPattern δ σ T D₁ η C Y X L
    shiftedZero baseColor hlocal label r hlabel hT hY hN hσ hη.le hC
    (hCoeff Y X) hinterval hlarge hsep


end TaoTrudgianYang2025
