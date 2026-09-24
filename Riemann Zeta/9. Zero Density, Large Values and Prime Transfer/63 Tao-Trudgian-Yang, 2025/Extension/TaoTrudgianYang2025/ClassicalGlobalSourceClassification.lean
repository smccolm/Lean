import TaoTrudgianYang2025.ClassicalGlobalTerminalSource

/-!
# Exhaustive occupied global source classification

At sufficiently large height, every genuinely large global source block
is either one of the two bottom blocks or an interior block of physical
logarithmic scale greater than one. Terminal blocks are excluded at the
same actual ordinate. No subset or multiplicity loss is introduced.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_large_global_source_classification
    (s d u : ℝ) (hs : 1/2 < s) (hsUpper : s < 1)
    (hd : 0 < d) (hdGap : d ≤ (s-1/2)/1000) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (Y A r : ℕ), T₀ ≤ T →
      A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y →
      T-T^d ≤ t → t ≤ 2*T+T^d →
      ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r s t‖ →
      r < 2 ∨
        (((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) ∧
          2*(2^r*Y) ≤ A ∧ 1 < typeILogarithmicScale T (2^r*Y)) := by
  have hdOne : d < 1 := by linarith
  have huGap : u < s-1/2 := by linarith
  obtain ⟨Tterminal,hTterminal,hTerminal⟩ :=
    eventually_no_terminal_global_source_point s d u hs hdOne huGap
  obtain ⟨Tmargin,_hTmargin,hMargin⟩ :=
    eventually_large_source_forces_complementary_margin hsUpper hd hdOne hdGap huD
  obtain ⟨Tdisp,_hTdisp,hDisp⟩ := eventually_rpow_le_half_self d hdOne
  refine ⟨max Tterminal (max Tmargin Tdisp),
    hTterminal.trans (le_max_left _ _),?_⟩
  intro T t Y A r hT hA hY hLower hUpper hLarge
  by_cases hr : r < 2
  · exact Or.inl hr
  have hrTwo : 2 ≤ r := by omega
  rcases typeISourceSmoothScale_lower_terminal_or_interior
      (Y := Y) (A := A) (r := r) (by omega : 1 ≤ Y) with hBottom | hEdge | hInterior
  · exact (hr hBottom).elim
  · exact (hTerminal T t Y A r ((le_max_left _ _).trans hT)
      hA hY hrTwo hEdge hLower hUpper hLarge).elim
  · have hTMargin : Tmargin ≤ T :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hT)
    have hTDisp : Tdisp ≤ T :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hT)
    have hMarginAt := hMargin T t (typeILogarithmicScale T (2^r*Y)) Y A r
      hTMargin hA hY hrTwo hInterior.2 hLower hUpper (hDisp T hTDisp) rfl hLarge
    exact Or.inr ⟨hInterior.1,hInterior.2,by linarith⟩

theorem eventually_classicalTypeI_global_source_classification
    (s d u : ℝ) (hs : 1/2 < s) (hsUpper : s < 1)
    (hd : 0 < d) (hdGap : d ≤ (s-1/2)/1000) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T : ℝ) (Y X L : ℕ), T₀ ≤ T →
    ∀ (shiftedZero : ↥(zerosInRect s 1 T (2*T)) → ℝ)
    (baseColor : ↥(zerosInRect s 1 T (2*T)) → ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset (fun x : ClassicalSlabZeroCopy s T => shiftedZero x.1) z).card ≤ L)
    (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (_ : branchLabel.1 = some (Sum.inl r)) (_ : 1 ≤ Y)
    (_ : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel,
      ClassicalBranchScaleLarge s T u Y X branchLabel.1 (shiftedZero x.1.1))
    (_ : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel,
      x ≠ y → 1 ≤ |shiftedZero x.1.1-shiftedZero y.1.1|)
    (_ : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel,
      T-T^d ≤ shiftedZero x.1.1 ∧ shiftedZero x.1.1 ≤ 2*T+T^d),
    let A := ⌊sharpZetaCutoff T⌋₊
    let V := (3/4)*(T^(-u)/2)
    let ι := EnergyColorFiber
      (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel
    let W : ι → ℝ := fun x => shiftedZero x.1.1
    ∃ label : ι → Fin (Nat.clog 2 A+1),
      (∀ x, V/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A (label x).val s (W x)‖) ∧
      (∀ x, (label x).val < 2 ∨ A < 2*(2^(label x).val*Y) ∨
        (((Y+1 : ℕ) : ℝ) ≤ (((2^(label x).val*Y : ℕ) : ℝ)/2) ∧
          2*(2^(label x).val*Y) ≤ A)) ∧
      (∀ (c : Fin (Nat.clog 2 A+1)) (x y : EnergyColorFiber label c),
        x ≠ y → 1 ≤ |W x.1-W y.1|) ∧
      Fintype.card ι = ∑ c : Fin (Nat.clog 2 A+1),
        Fintype.card (EnergyColorFiber label c) ∧
      (∃ chosen : Fin 4 → Fin (Nat.clog 2 A+1),
        let Wᵢ := fun i : Fin 4 => fun x : EnergyColorFiber label (chosen i) => W x.1
        4*(approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9*(Nat.clog 2 A+1 : ℕ)^4*
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) ∧
      (∀ x, (label x).val < 2 ∨
        (((Y+1 : ℕ) : ℝ) ≤ (((2^(label x).val*Y : ℕ) : ℝ)/2) ∧
          2*(2^(label x).val*Y) ≤ A ∧
          1 < typeILogarithmicScale T (2^(label x).val*Y))) := by
  obtain ⟨T₀,hT₀,hPoint⟩ :=
    eventually_large_global_source_classification s d u hs hsUpper hd hdGap huD
  refine ⟨T₀,hT₀,?_⟩
  intro T Y X L hT shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep hRange
  dsimp only
  obtain ⟨label,hValues,hClass,hSeparated,hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels
      s T u Y X L shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep
  refine ⟨label,hValues,hClass,hSeparated,hCard,hEnergy,?_⟩
  intro x
  exact hPoint T (shiftedZero x.1.1) Y ⌊sharpZetaCutoff T⌋₊ (label x).val
    hT rfl (by omega) (hRange x).1 (hRange x).2 (hValues x)

end TaoTrudgianYang2025
