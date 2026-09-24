import TaoTrudgianYang2025.ClassicalGlobalSourceEntry

/-!
# Full-index dyadic extraction from global smooth sources

Normalize the actual source coefficients and choose a dyadic label for
every original index. Nonzero support proves the physical length window.
No ordinate is moved and no cardinality-selected subfamily is substituted.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem normalized_source_dyadic_nonzero_scale
    (Y A r N : ℕ) (s t : ℝ)
    (hPoly : dirichletPoly N (normalizedTypeISourceDirichletCoeff Y A r s) t ≠ 0) :
    N < 2*(2^r*Y) ∧ 2^r*Y < 4*N := by
  unfold dirichletPoly at hPoly
  obtain ⟨n,hn,hnTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPoly
  have hnWeight : typeISourceSmoothWeight Y A r n ≠ 0 := by
    intro hzero
    apply hnTerm
    simp [normalizedTypeISourceDirichletCoeff,typeISourceDirichletCoeff,hzero]
  have hnSource := typeISourceSmoothWeight_support hnWeight
  have hnDyadic := Finset.mem_Ioc.mp hn
  have hLeftReal : (N : ℝ) < 2*(2^r*Y : ℕ) := by
    have hPn : (N : ℝ) < n := by exact_mod_cast hnDyadic.1
    exact hPn.trans hnSource.2
  have hRightReal : ((2^r*Y : ℕ) : ℝ) < 4*N := by
    have hnUpper : (n : ℝ) ≤ 2*N := by exact_mod_cast hnDyadic.2
    nlinarith [hnSource.1]
  exact ⟨by exact_mod_cast hLeftReal,by exact_mod_cast hRightReal⟩

theorem exists_source_normalized_indexed_dyadic_family
    {ι : Type*} [Fintype ι]
    (Y A r : ℕ) (s V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hA : 1 < A) (hs : 0 ≤ s) (hV : 0 < V)
    (hLarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r s (W x)‖) :
    let k := Nat.clog 2 (A+1)
    let Q := 2^r*Y
    ∃ label : ι → Fin k,
      (∀ n, ‖normalizedTypeISourceDirichletCoeff Y A r s n‖ ≤ 1) ∧
      (∀ x,
        (((Q : ℝ)/2)^s*V)/k ≤
          ‖dirichletPoly (2^(label x).val)
            (normalizedTypeISourceDirichletCoeff Y A r s) (W x)‖) ∧
      (∀ x, 2^(label x).val < 2*Q ∧ Q < 4*2^(label x).val) ∧
      Fintype.card ι = ∑ c : Fin k, Fintype.card (EnergyColorFiber label c) ∧
      ∃ chosen : Fin 4 → Fin k,
        let Wᵢ := fun i : Fin 4 => fun x : EnergyColorFiber label (chosen i) => W x.1
        4*(approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9*(k : ℝ)^4*
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
  classical
  dsimp only
  let k := Nat.clog 2 (A+1)
  let Q := 2^r*Y
  have hk : 0 < k := Nat.clog_pos Nat.one_lt_two (by omega)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hScale : 0 < ((Q : ℝ)/2)^s := Real.rpow_pos_of_pos (by positivity) _
  have hWide : ∀ x, ((Q : ℝ)/2)^s*V ≤
      ‖wideDirichletPoly 1 k (normalizedTypeISourceDirichletCoeff Y A r s) (W x)‖ := by
    intro x
    rw [wideDirichletPoly_normalizedTypeISourceDirichletCoeff Y A r s (W x) hY,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hScale]
    exact mul_le_mul_of_nonneg_left (hLarge x) hScale.le
  have hBlocks : ∀ x, ∃ j ∈ Finset.range k,
      (((Q : ℝ)/2)^s*V)/k ≤
        ‖dirichletPoly (2^j) (normalizedTypeISourceDirichletCoeff Y A r s) (W x)‖ := by
    intro x
    simpa only [mul_one] using exists_large_dyadic_block 1 k
      (normalizedTypeISourceDirichletCoeff Y A r s) (W x)
      (((Q : ℝ)/2)^s*V) hk (hWide x)
  choose j hj hValue using hBlocks
  let label : ι → Fin k := fun x => ⟨j x,Finset.mem_range.mp (hj x)⟩
  refine ⟨label,norm_normalizedTypeISourceDirichletCoeff_le_one Y A r s hs,
    hValue,?_,cardinality_eq_sum_color_fibers label,?_⟩
  · intro x
    have hThreshold : 0 < (((Q : ℝ)/2)^s*V)/k := by positivity
    have hPoly : dirichletPoly (2^(label x).val)
        (normalizedTypeISourceDirichletCoeff Y A r s) (W x) ≠ 0 := by
      intro hzero
      have hx := hValue x
      change _ ≤ ‖dirichletPoly (2^(label x).val)
        (normalizedTypeISourceDirichletCoeff Y A r s) (W x)‖ at hx
      rw [hzero,norm_zero] at hx
      linarith
    exact normalized_source_dyadic_nonzero_scale Y A r (2^(label x).val) s (W x) hPoly
  · letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
    obtain ⟨chosen,hEnergy⟩ := exists_energy_color_classes W label
    refine ⟨chosen,?_⟩
    simpa only [Fintype.card_fin] using hEnergy

end TaoTrudgianYang2025
