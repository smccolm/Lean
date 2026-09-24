import TaoTrudgianYang2025.ClassicalGlobalSourceEntry
import TaoTrudgianYang2025.ClassicalReflectedLineUniformity

/-!
# Interior reflected bounds on actual detector source classes

Global source labels retain every analytic-multiplicity copy. The common
line window, displacement exponent and estimate constant precede the
detector's shifted source line. Only the interior fibers of physical
logarithmic scale strictly between one and two are bounded here; the
other source branches remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_global_interior_source_cardinality_bounds
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (8/(sigma-1/2)),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (sigma-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → s ≤ sigma → 0 ≤ u → u ≤ d →
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
      (∀ c : Fin (Nat.clog 2 A+1), 2 ≤ c.val →
        ((Y+1 : ℕ) : ℝ) ≤ (((2^c.val*Y : ℕ) : ℝ)/2) →
        2*(2^c.val*Y) ≤ A →
        1 < typeILogarithmicScale T (2^c.val*Y) →
        typeILogarithmicScale T (2^c.val*Y) < 2 →
        (Fintype.card (EnergyColorFiber label c) : ℝ) ≤ C*T^(B+ε)) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEpsilon,C,hC,hBounds⟩ :=
    classicalReflected_uniform_shifted_line_source_cardinality_bound
      sigma B hsigma hsigmaUpper hB hLV ε hε
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEpsilon,C,hC,?_⟩
  intro s u hsLower hsUpper hu huD
  obtain ⟨T₀,hT₀,hBound⟩ := hBounds s u hsLower hsUpper hu huD
  refine ⟨T₀,hT₀,?_⟩
  intro T Y X L hT shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep hRange
  dsimp only
  obtain ⟨label,hValues,hClass,hSeparated,hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels
      s T u Y X L shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep
  refine ⟨label,hValues,hClass,hSeparated,hCard,hEnergy,?_⟩
  intro c hc hLower hUpper hTauOne hTauTwo
  apply hBound (fun x : EnergyColorFiber label c => shiftedZero x.1.1.1)
    hT rfl (by omega) hc hLower hUpper rfl hTauOne hTauTwo
  · intro x
    exact hRange x.1
  · intro x
    have hx := hValues x.1
    rw [x.2] at hx
    exact hx
  · exact hSeparated c

theorem classicalTypeI_global_interior_source_energy_bounds
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (8/(sigma-1/2)),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (sigma-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → s ≤ sigma → 0 ≤ u → u ≤ d →
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
      (∀ c : Fin (Nat.clog 2 A+1), 2 ≤ c.val →
        ((Y+1 : ℕ) : ℝ) ≤ (((2^c.val*Y : ℕ) : ℝ)/2) →
        2*(2^c.val*Y) ≤ A →
        1 < typeILogarithmicScale T (2^c.val*Y) →
        typeILogarithmicScale T (2^c.val*Y) < 2 →
        (approximateAdditiveEnergyOf 1 (fun x : EnergyColorFiber label c => W x.1) : ℝ) ≤ C*T^(B+ε)) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEpsilon,C,hC,hBounds⟩ :=
    classicalReflected_uniform_shifted_line_source_energy_bound
      sigma B hsigma hsigmaUpper hB hLV ε hε
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEpsilon,C,hC,?_⟩
  intro s u hsLower hsUpper hu huD
  obtain ⟨T₀,hT₀,hBound⟩ := hBounds s u hsLower hsUpper hu huD
  refine ⟨T₀,hT₀,?_⟩
  intro T Y X L hT shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep hRange
  dsimp only
  obtain ⟨label,hValues,hClass,hSeparated,hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels
      s T u Y X L shiftedZero baseColor hlocal branchLabel r hlabel hY hlarge hsep
  refine ⟨label,hValues,hClass,hSeparated,hCard,hEnergy,?_⟩
  intro c hc hLower hUpper hTauOne hTauTwo
  apply hBound (fun x : EnergyColorFiber label c => shiftedZero x.1.1.1)
    hT rfl (by omega) hc hLower hUpper rfl hTauOne hTauTwo
  · intro x
    exact hRange x.1
  · intro x
    have hx := hValues x.1
    rw [x.2] at hx
    exact hx
  · exact hSeparated c

end TaoTrudgianYang2025
