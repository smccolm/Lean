import TaoTrudgianYang2025.ClassicalDirectSourceBounds

/-!
# Direct large-scale bounds on the actual global detector fibers

The original analytic-multiplicity-copy class supplies its global smooth
labels. Every legal interior fiber of physical scale at least two is
bounded, while its full cardinality partition and energy decomposition
remain visible for the subsequent slab assembly.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_global_direct_source_cardinality_bounds
    (sigma B a : ℝ) (hsigma : 1/2 < sigma)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ 1/4 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                ∀ X L : ℕ,
    ∀ (shiftedZero : ↥(zerosInRect s 1 T (2*T)) → ℝ)
    (baseColor : ↥(zerosInRect s 1 T (2*T)) → ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset (fun x : ClassicalSlabZeroCopy s T => shiftedZero x.1) z).card ≤ L)
    (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (_ : branchLabel.1 = some (Sum.inl r))
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
        2 ≤ typeILogarithmicScale T (2^c.val*Y) →
        (Fintype.card (EnergyColorFiber label c) : ℝ) ≤ C*T^(B+ε)) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,C,hC,hBounds⟩ :=
    classicalDirect_uniform_shifted_line_source_cardinality_bound
      sigma B a hsigma hB ha haHalf hLV ε hε
  refine ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,C,hC,?_⟩
  intro s u hsLower hu huD
  have hPowerEvent := (tendsto_rpow_atTop ha).eventually
    (Filter.eventually_ge_atTop (2 : ℝ))
  filter_upwards [hBounds s u hsLower hu huD,hPowerEvent] with T hBoundsT hPower
  dsimp only
  intro X L shiftedZero baseColor hlocal branchLabel r hlabel hlarge hsep hRange
  have hYTwo : 2 ≤ ⌊T^a⌋₊ := Nat.le_floor hPower
  obtain ⟨label,hValues,hClass,hSeparated,hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels
      s T u ⌊T^a⌋₊ X L shiftedZero baseColor hlocal branchLabel r hlabel
      (by omega) hlarge hsep
  refine ⟨label,hValues,hClass,hSeparated,hCard,hEnergy,?_⟩
  intro c hc hLower hUpper hScale
  apply hBoundsT c.val (fun x : EnergyColorFiber label c => shiftedZero x.1.1.1)
    hc hLower hUpper hScale
  · intro x
    exact hRange x.1
  · intro x
    have hx := hValues x.1
    rw [x.2] at hx
    exact hx
  · exact hSeparated c

theorem classicalTypeI_global_direct_source_energy_bounds
    (sigma B a : ℝ) (hsigma : 1/2 < sigma)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (sigma-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ 1/4 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, sigma-eta ≤ s → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                ∀ X L : ℕ,
    ∀ (shiftedZero : ↥(zerosInRect s 1 T (2*T)) → ℝ)
    (baseColor : ↥(zerosInRect s 1 T (2*T)) → ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset (fun x : ClassicalSlabZeroCopy s T => shiftedZero x.1) z).card ≤ L)
    (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (_ : branchLabel.1 = some (Sum.inl r))
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
        2 ≤ typeILogarithmicScale T (2^c.val*Y) →
        (approximateAdditiveEnergyOf 1 (fun x : EnergyColorFiber label c => W x.1) : ℝ) ≤ C*T^(B+ε)) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,C,hC,hBounds⟩ :=
    classicalDirect_uniform_shifted_line_source_energy_bound
      sigma B a hsigma hB ha haHalf hLV ε hε
  refine ⟨eta,hEta,hEtaGap,d,hd,hdQuarter,hdEpsilon,C,hC,?_⟩
  intro s u hsLower hu huD
  have hPowerEvent := (tendsto_rpow_atTop ha).eventually
    (Filter.eventually_ge_atTop (2 : ℝ))
  filter_upwards [hBounds s u hsLower hu huD,hPowerEvent] with T hBoundsT hPower
  dsimp only
  intro X L shiftedZero baseColor hlocal branchLabel r hlabel hlarge hsep hRange
  have hYTwo : 2 ≤ ⌊T^a⌋₊ := Nat.le_floor hPower
  obtain ⟨label,hValues,hClass,hSeparated,hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels
      s T u ⌊T^a⌋₊ X L shiftedZero baseColor hlocal branchLabel r hlabel
      (by omega) hlarge hsep
  refine ⟨label,hValues,hClass,hSeparated,hCard,hEnergy,?_⟩
  intro c hc hLower hUpper hScale
  apply hBoundsT c.val (fun x : EnergyColorFiber label c => shiftedZero x.1.1.1)
    hc hLower hUpper hScale
  · intro x
    exact hRange x.1
  · intro x
    have hx := hValues x.1
    rw [x.2] at hx
    exact hx
  · exact hSeparated c

end TaoTrudgianYang2025
