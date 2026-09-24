import TaoTrudgianYang2025.ClassicalGlobalSourceLabels

/-!
# Global smooth entry from the actual multiplicity-copy Type-I class

The second component of the detector's Type-I assertion is the full
long-tail lower bound at the same ordinate. It supplies global smooth
labels on the original color-fiber index type. No local Fin-2 smoothing
or cardinality-selected subset is substituted for this source.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_classicalTypeI_global_source_indexed_labels
    (sigma T D : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect sigma 1 T (2*T)) → ℝ)
    (baseColor : ↥(zerosInRect sigma 1 T (2*T)) → ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset (fun x : ClassicalSlabZeroCopy sigma T => shiftedZero x.1) z).card ≤ L)
    (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (hlabel : branchLabel.1 = some (Sum.inl r)) (hY : 1 ≤ Y)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor sigma T Y shiftedZero baseColor L hlocal) branchLabel,
      ClassicalBranchScaleLarge sigma T D Y X branchLabel.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor sigma T Y shiftedZero baseColor L hlocal) branchLabel,
      x ≠ y → 1 ≤ |shiftedZero x.1.1-shiftedZero y.1.1|) :
    let A := ⌊sharpZetaCutoff T⌋₊
    let V := (3/4)*(T^(-D)/2)
    let ι := EnergyColorFiber
      (classicalSeparatedBranchScaleColor sigma T Y shiftedZero baseColor L hlocal) branchLabel
    let W : ι → ℝ := fun x => shiftedZero x.1.1
    ∃ label : ι → Fin (Nat.clog 2 A+1),
      (∀ x, V/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A (label x).val sigma (W x)‖) ∧
      (∀ x, (label x).val < 2 ∨ A < 2*(2^(label x).val*Y) ∨
        (((Y+1 : ℕ) : ℝ) ≤ (((2^(label x).val*Y : ℕ) : ℝ)/2) ∧
          2*(2^(label x).val*Y) ≤ A)) ∧
      (∀ (c : Fin (Nat.clog 2 A+1)) (x y : EnergyColorFiber label c),
        x ≠ y → 1 ≤ |W x.1-W y.1|) ∧
      Fintype.card ι = ∑ c : Fin (Nat.clog 2 A+1),
        Fintype.card (EnergyColorFiber label c) ∧
      ∃ chosen : Fin 4 → Fin (Nat.clog 2 A+1),
        let Wᵢ := fun i : Fin 4 => fun x : EnergyColorFiber label (chosen i) => W x.1
        4*(approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9*(Nat.clog 2 A+1 : ℕ)^4*
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
  classical
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let V := (3/4)*(T^(-D)/2)
  let ι := EnergyColorFiber
    (classicalSeparatedBranchScaleColor sigma T Y shiftedZero baseColor L hlocal) branchLabel
  let W : ι → ℝ := fun x => shiftedZero x.1.1
  have hLong : ∀ x, V ≤ ‖classicalZetaLongTail Y A
      ((sigma : ℂ)+Complex.I*(W x : ℂ))‖ := by
    intro x
    have hx := hlarge x
    rw [hlabel] at hx
    simpa only [ClassicalBranchScaleLarge,ClassicalTypeILargeAt,A,V,W] using hx.2
  obtain ⟨label,hValues,hClass,hCard⟩ :=
    exists_global_typeISourceSmoothBlock_indexed_labels Y A (Nat.clog 2 A)
      sigma V W hY (sharp_source_cutoff_le_clog_cover hY) hLong
  refine ⟨label,hValues,hClass,?_,hCard,?_⟩
  · intro c x y hxy
    exact hsep x.1 y.1 (fun h => hxy (Subtype.ext h))
  · obtain ⟨chosen,hEnergy⟩ := exists_energy_color_classes W label
    refine ⟨chosen,?_⟩
    simpa only [Fintype.card_fin] using hEnergy

end TaoTrudgianYang2025

