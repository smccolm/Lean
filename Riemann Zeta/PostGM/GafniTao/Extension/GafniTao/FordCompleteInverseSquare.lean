import GafniTao.FordGlobalInverseSquare

/-!
# Local/nonlocal assembly of Ford's inverse-square zero sum
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordFiniteInverseSquareOutside
    (t T v : ℝ) : ℝ :=
  ∑ rho ∈ (zeroSet 0 T).filter (fun rho =>
      v ≤ fordLocalDistance t rho),
    (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2

theorem mem_fordLocalDiskZeros_of_mem_zeroSet_of_distance_le
    {t T q : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet 0 T)
    (hdist : fordLocalDistance t rho ≤ q) :
    rho ∈ fordLocalDiskZeros t q := by
  have hdata := mem_zeroSet_zero_data hrho
  have himDist : |t - rho.im| ≤ fordLocalDistance t rho := by
    simpa [fordLocalDistance, mul_comm] using
      Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * I - rho)
  have himAbs : |rho.im| ≤ |t| + q := by
    calc
      |rho.im| = |t - (t - rho.im)| := by ring_nf
      _ ≤ |t| + |t - rho.im| := abs_sub _ _
      _ ≤ |t| + q := by linarith
  rw [mem_fordLocalDiskZeros_iff]
  constructor
  · change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (- (|t| + q)) (|t| + q)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    exact ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (- (|t| + q)) (|t| + q) rho).mpr
        ⟨hdata.1, hdata.2.1, (abs_le.mp himAbs).1,
          (abs_le.mp himAbs).2⟩, hdata.2.2.2.2⟩
  · exact hdist

theorem fordFiniteInverseSquareOutside_le_local_add_nonlocal
    {t T v q : ℝ} :
    fordFiniteInverseSquareOutside t T v ≤
      fordLocalAnnularInverseSquare t v q +
        fordNonlocalInverseSquare t T q := by
  let S := (zeroSet 0 T).filter (fun rho => v ≤ fordLocalDistance t rho)
  let L := S.filter (fun rho => fordLocalDistance t rho < q)
  let G := S.filter (fun rho => q ≤ fordLocalDistance t rho)
  have hsplit : S = L ∪ G := by
    ext rho
    simp only [L, G, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      by_cases hd : fordLocalDistance t rho < q
      · exact Or.inl ⟨h, hd⟩
      · exact Or.inr ⟨h, le_of_not_gt hd⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have htermNonneg (rho : ℂ) :
      0 ≤ (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 := by
    positivity
  have hdisjoint : Disjoint L G := by
    apply Finset.disjoint_left.mpr
    intro rho hL hG
    rw [Finset.mem_filter] at hL hG
    exact (not_lt_of_ge hG.2) hL.2
  have hLocalSubset : L ⊆ fordLocalAnnulus t v q := by
    intro rho hrho
    rw [Finset.mem_filter] at hrho
    have hS := Finset.mem_filter.mp hrho.1
    have hDisk := mem_fordLocalDiskZeros_of_mem_zeroSet_of_distance_le
      hS.1 hrho.2.le
    rw [fordLocalAnnulus, Finset.mem_filter]
    exact ⟨hDisk, hS.2⟩
  have hGlobalSubset : G ⊆
      (zeroSet 0 T).filter (fun rho => q ≤ fordLocalDistance t rho) := by
    intro rho hrho
    rw [Finset.mem_filter] at hrho ⊢
    exact ⟨(Finset.mem_filter.mp hrho.1).1, hrho.2⟩
  unfold fordFiniteInverseSquareOutside
  change ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) /
      fordLocalDistance t rho ^ 2 ≤ _
  rw [hsplit]
  calc
    ∑ rho ∈ L ∪ G, (zeroMultiplicity rho : ℝ) /
        fordLocalDistance t rho ^ 2 =
      (∑ rho ∈ L, (zeroMultiplicity rho : ℝ) /
        fordLocalDistance t rho ^ 2) +
      ∑ rho ∈ G, (zeroMultiplicity rho : ℝ) /
        fordLocalDistance t rho ^ 2 :=
      Finset.sum_union hdisjoint
    _ ≤ (∑ rho ∈ fordLocalAnnulus t v q,
          (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2) +
        ∑ rho ∈ (zeroSet 0 T).filter
          (fun rho => q ≤ fordLocalDistance t rho),
          (zeroMultiplicity rho : ℝ) / fordLocalDistance t rho ^ 2 := by
      apply add_le_add
      · exact Finset.sum_le_sum_of_subset_of_nonneg hLocalSubset
          (fun rho _ _ => htermNonneg rho)
      · exact Finset.sum_le_sum_of_subset_of_nonneg hGlobalSubset
          (fun rho _ _ => htermNonneg rho)
    _ = fordLocalAnnularInverseSquare t v q +
        fordNonlocalInverseSquare t T q := by
      rfl

/-- Uniform complete finite inverse-square estimate at Ford's standard outer
radius `1/4`. -/
theorem fordFiniteInverseSquareOutside_le_general
    {A B t T v : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (ht : 100 ≤ t)
    (hv : 0 < v) (hvUpper : v ≤ 1 / 4) :
    fordFiniteInverseSquareOutside t T v ≤
      fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v / v ^ 2 +
            20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) +
        225 * globalLocalZeroLogConstant *
          (Real.log (fordAdaptiveZeroBinHeight ⌊t⌋) *
              fordInverseSquareBinMass +
            fordInverseSquareBinLogMass) := by
  have hsplit := fordFiniteInverseSquareOutside_le_local_add_nonlocal
    (t := t) (T := T) (v := v) (q := (1 / 4 : ℝ))
  have hlocal := fordLocalAnnularInverseSquare_le_general_sharp
    hFord hA hB ht hv hvUpper le_rfl
  have hglobal := fordNonlocalInverseSquare_le
    (t := t) (T := T) (q := (1 / 4 : ℝ)) le_rfl
  linarith

#print axioms fordFiniteInverseSquareOutside_le_general

end

end GafniTao
