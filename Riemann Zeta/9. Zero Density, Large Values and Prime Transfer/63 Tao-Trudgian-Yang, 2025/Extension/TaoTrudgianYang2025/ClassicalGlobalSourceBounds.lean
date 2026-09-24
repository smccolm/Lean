import TaoTrudgianYang2025.ClassicalGlobalBlockBounds

/-!
# Single-labeling full Type-I source-class bounds

One global labeling is selected from the actual detector class. The common
bottom/reflected/direct estimate is applied to those identical fibers.
The outer smooth-label loss is absorbed for cardinality and for the full
four-fiber energy estimate, retaining every analytic multiplicity copy.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_uniform_global_source_class_cardinality_bound
    (σ B a : ℝ) (hσ : 1/2 < σ) (hσOne : σ < 1)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (σ-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (σ-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, σ-eta ≤ s → s ≤ σ → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                ∀ (X L : ℕ)
                  (shiftedZero : ↥(zerosInRect s 1 T (2*T)) → ℝ)
                  (baseColor : ↥(zerosInRect s 1 T (2*T)) → ClassicalBranchScaleColor T Y)
                  (hlocal : ∀ z : ℤ,
                    (unitBinFinset (fun x : ClassicalSlabZeroCopy s T => shiftedZero x.1) z).card ≤ L)
                  (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
                  (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)),
                  branchLabel.1 = some (Sum.inl r) →
                  (∀ ρ, T-T^d ≤ shiftedZero ρ ∧ shiftedZero ρ ≤ 2*T+T^d) →
                  (∀ x : EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel,
                    ClassicalBranchScaleLarge s T u Y X branchLabel.1 (shiftedZero x.1.1)) →
                  (Fintype.card (EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel) : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEps,C,hC,hBlocks⟩ :=
    classicalGlobal_uniform_source_block_cardinality_bound σ B a hσ hσOne hB ha haHalf
      hZeta hGeneral (ε/2) (by positivity)
  let Cfinal := max 1 (C)
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,by linarith,Cfinal,le_max_left _ _,?_⟩
  intro s u hsLower hsUpper hu huD
  filter_upwards [hBlocks s u hsLower hsUpper hu huD,
    eventually_const_mul_classicalTypeI_clog_le_rpow 2 (ε/8)
      (by norm_num) (by positivity),
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)] with T hBlocksT hLog hPower hT
  dsimp only
  intro X L shiftedZero baseColor hlocal branchLabel r hLabel hRange hLarge
  classical
  let Y := ⌊T^a⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let ι := EnergyColorFiber
    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel
  let W : ι → ℝ := fun x => shiftedZero x.1.1
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 1 ≤ Y := by
    have hTwo : 2 ≤ Y := Nat.le_floor hPower
    omega
  have hA : 1 < A := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hSep : ∀ x y : ι, x ≠ y → 1 ≤ |W x-W y| := by
    intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy s T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal branchLabel x y hxy
  obtain ⟨label,hValues,_hClass,hSeparated,_hCard,_hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels s T u Y X L shiftedZero baseColor hlocal
      branchLabel r hLabel hY hLarge hSep
  let Wᵢ := fun c : Fin (Nat.clog 2 A+1) => fun x : EnergyColorFiber label c => W x.1
  let E := C*T^(B+ε/2)
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  have hClass (c : Fin (Nat.clog 2 A+1)) :
      (Fintype.card (EnergyColorFiber label c) : ℝ) ≤ E := by
    apply hBlocksT c.val (Wᵢ c) (hSeparated c)
    · intro x
      exact hRange x.1.1.1
    · intro x
      have hx := hValues x.1
      rw [x.2] at hx
      exact hx
  let k : ℝ := (Nat.clog 2 A+1 : ℕ)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hkSmall : k ≤ T^(ε/8) := by
    have hClog : (1 : ℝ) ≤ Nat.clog 2 A := by
      exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
    calc
      k ≤ 2*(Nat.clog 2 A : ℝ) := by dsimp [k]; push_cast; linarith
      _ ≤ T^(ε/8) := hLog
  have hkPower : k ≤ T^(ε/2) :=
    hkSmall.trans (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
  have hTotal : (Fintype.card ι : ℝ) ≤ k*E := by
    simpa only [Fintype.card_fin] using cardinality_le_color_count_mul label E hClass
  calc
    (Fintype.card ι : ℝ) ≤ k*E := hTotal
    _ ≤ T^(ε/2)*E := mul_le_mul_of_nonneg_right hkPower (by dsimp [E]; positivity)
    _ = C*T^(B+ε) := by
      dsimp only [E]
      rw [show B+ε = ε/2+(B+ε/2) by ring,Real.rpow_add hTPos (ε/2) (B+ε/2)]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)


theorem classicalTypeI_uniform_global_source_class_energy_bound
    (σ B a : ℝ) (hσ : 1/2 < σ) (hσOne : σ < 1)
    (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc (1/(2*a)) (2/a), IsLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ (σ-1/2)/2 ∧
        ∃ d : ℝ, 0 < d ∧ d ≤ (σ-1/2)/2000 ∧ d ≤ ε/100 ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ s u : ℝ, σ-eta ≤ s → s ≤ σ → 0 ≤ u → u ≤ d →
              ∀ᶠ T : ℝ in Filter.atTop,
                let Y := ⌊T^a⌋₊
                ∀ (X L : ℕ)
                  (shiftedZero : ↥(zerosInRect s 1 T (2*T)) → ℝ)
                  (baseColor : ↥(zerosInRect s 1 T (2*T)) → ClassicalBranchScaleColor T Y)
                  (hlocal : ∀ z : ℤ,
                    (unitBinFinset (fun x : ClassicalSlabZeroCopy s T => shiftedZero x.1) z).card ≤ L)
                  (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
                  (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)),
                  branchLabel.1 = some (Sum.inl r) →
                  (∀ ρ, T-T^d ≤ shiftedZero ρ ∧ shiftedZero ρ ≤ 2*T+T^d) →
                  (∀ x : EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel,
                    ClassicalBranchScaleLarge s T u Y X branchLabel.1 (shiftedZero x.1.1)) →
                  (approximateAdditiveEnergyOf 1 (fun x : EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel =>
                      shiftedZero x.1.1) : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨eta,hEta,hEtaGap,d,hd,hdGap,hdEps,C,hC,hBlocks⟩ :=
    classicalGlobal_uniform_source_block_energy_bound σ B a hσ hσOne hB ha haHalf
      hZeta hGeneral (ε/2) (by positivity)
  let Cfinal := max 1 (9*C)
  refine ⟨eta,hEta,hEtaGap,d,hd,hdGap,by linarith,Cfinal,le_max_left _ _,?_⟩
  intro s u hsLower hsUpper hu huD
  filter_upwards [hBlocks s u hsLower hsUpper hu huD,
    eventually_const_mul_classicalTypeI_clog_le_rpow 2 (ε/8)
      (by norm_num) (by positivity),
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Filter.eventually_ge_atTop (8 : ℝ)] with T hBlocksT hLog hPower hT
  dsimp only
  intro X L shiftedZero baseColor hlocal branchLabel r hLabel hRange hLarge
  classical
  let Y := ⌊T^a⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let ι := EnergyColorFiber
    (classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal) branchLabel
  let W : ι → ℝ := fun x => shiftedZero x.1.1
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hY : 1 ≤ Y := by
    have hTwo : 2 ≤ Y := Nat.le_floor hPower
    omega
  have hA : 1 < A := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hSep : ∀ x y : ι, x ≠ y → 1 ≤ |W x-W y| := by
    intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy s T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal branchLabel x y hxy
  obtain ⟨label,hValues,_hClass,hSeparated,_hCard,hEnergy⟩ :=
    exists_classicalTypeI_global_source_indexed_labels s T u Y X L shiftedZero baseColor hlocal
      branchLabel r hLabel hY hLarge hSep
  let Wᵢ := fun c : Fin (Nat.clog 2 A+1) => fun x : EnergyColorFiber label c => W x.1
  let E := C*T^(B+ε/2)
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  have hClass (c : Fin (Nat.clog 2 A+1)) :
      (approximateAdditiveEnergyOf 1 (Wᵢ c) : ℝ) ≤ E := by
    apply hBlocksT c.val (Wᵢ c) (hSeparated c)
    · intro x
      exact hRange x.1.1.1
    · intro x
      have hx := hValues x.1
      rw [x.2] at hx
      exact hx
  let k : ℝ := (Nat.clog 2 A+1 : ℕ)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hkSmall : k ≤ T^(ε/8) := by
    have hClog : (1 : ℝ) ≤ Nat.clog 2 A := by
      exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
    calc
      k ≤ 2*(Nat.clog 2 A : ℝ) := by dsimp [k]; push_cast; linarith
      _ ≤ T^(ε/8) := hLog
  obtain ⟨chosen,hEnergy⟩ := hEnergy
  have hSum :
      (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 0)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 1)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 2)) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ (chosen 3)) : ℝ) ≤ 4*E := by
    linarith [hClass (chosen 0),hClass (chosen 1),hClass (chosen 2),hClass (chosen 3)]
  have hTotal : (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 9*k^4*E := by
    have hProd := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ 9*k^4)
    dsimp only at hEnergy
    nlinarith
  have hkPower : k^4 ≤ T^(ε/2) := by
    calc
      k^4 ≤ (T^(ε/8))^4 := pow_le_pow_left₀ hk hkSmall 4
      _ = T^(ε/2) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hTPos.le]
        congr 1
        ring
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 9*k^4*E := hTotal
    _ ≤ 9*T^(ε/2)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkPower (by norm_num)) (by dsimp [E]; positivity)
    _ = (9*C)*T^(B+ε) := by
      dsimp only [E]
      rw [show B+ε = ε/2+(B+ε/2) by ring,Real.rpow_add hTPos (ε/2) (B+ε/2)]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)


end TaoTrudgianYang2025
