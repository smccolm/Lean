import GafniTao.WooleySourceMean

/-!
# The source integer model specializes to the finite box model

This file embeds a coefficient family on `1,...,Q` into Wooley's actual
finitely supported integer sequence space.  The embedding is injective, so
no coefficients or residue classes are merged.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal source-box embedding `n : Fin Q ↦ n+1 : ℤ`. -/
def wooleyBoxIndexEmbedding (Q : ℕ) : Fin Q ↪ ℤ where
  toFun n := ((n : ℕ) + 1 : ℕ)
  inj' := by
    intro m n h
    apply Fin.ext
    change (((m : ℕ) + 1 : ℕ) : ℤ) = (((n : ℕ) + 1 : ℕ) : ℤ) at h
    exact Nat.add_right_cancel (Int.ofNat_inj.mp h)

@[simp] theorem wooleyBoxIndexEmbedding_apply {Q : ℕ} (n : Fin Q) :
    wooleyBoxIndexEmbedding Q n = (((n : ℕ) + 1 : ℕ) : ℤ) := rfl

/-- A finite box coefficient family, viewed as a finitely supported integer
sequence without changing its values. -/
def wooleyBoxSourceSequence {Q : ℕ} (gamma : Fin Q → ℂ) :
    WooleySourceSequence :=
  Finsupp.embDomain (wooleyBoxIndexEmbedding Q)
    (Finsupp.equivFunOnFinite.symm gamma)

@[simp] theorem wooleyBoxSourceSequence_apply_index {Q : ℕ}
    (gamma : Fin Q → ℂ) (n : Fin Q) :
    wooleyBoxSourceSequence gamma (wooleyBoxIndexEmbedding Q n) = gamma n := by
  rw [wooleyBoxSourceSequence, Finsupp.embDomain_apply_self]
  rfl

theorem wooleyBoxIndexEmbedding_injective (Q : ℕ) :
    Function.Injective (wooleyBoxIndexEmbedding Q) :=
  (wooleyBoxIndexEmbedding Q).injective

/-- The support is exactly the image of the nonzero box coefficients. -/
theorem wooleyBoxSourceSequence_support {Q : ℕ} (gamma : Fin Q → ℂ) :
    (wooleyBoxSourceSequence gamma).support =
      (Finset.univ.filter fun n : Fin Q => gamma n ≠ 0).map
        (wooleyBoxIndexEmbedding Q) := by
  rw [wooleyBoxSourceSequence, Finsupp.support_embDomain]
  ext n
  simp

/-- The source and box `L²` masses agree exactly. -/
theorem wooleyBoxSourceSequence_massSq {Q : ℕ} (gamma : Fin Q → ℂ) :
    wooleySourceMassSq (wooleyBoxSourceSequence gamma) =
      wooleyWeightedMassSq gamma := by
  rw [wooleySourceMassSq, wooleyWeightedMassSq,
    wooleyBoxSourceSequence_support]
  rw [Finset.sum_map]
  simp only [wooleyBoxSourceSequence_apply_index]
  apply Finset.sum_subset (by simp)
  intro n hn hnot
  have hnzero : gamma n = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_ne_iff] using hnot
  simp [hnzero]

/-- Residue `L²` masses agree under the box embedding. -/
theorem wooleySourceResidueMassSq_box {Q q : ℕ}
    (gamma : Fin Q → ℂ) (xi : ZMod q) :
    wooleySourceResidueMassSq (wooleyBoxSourceSequence gamma) q xi =
      wooleyWeightedResidueMassSq gamma xi := by
  unfold wooleySourceResidueMassSq wooleyWeightedResidueMassSq
    wooleyResidueClass
  rw [wooleyBoxSourceSequence_support]
  rw [Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_apply, wooleyBoxSourceSequence_apply_index]
  simp only [wooleyBoxIndexEmbedding_apply]
  have hcast (n : Fin Q) :
      (((((n : ℕ) + 1 : ℕ) : ℤ) : ZMod q)) =
        ((((n : ℕ) + 1 : ℕ) : ZMod q)) := by norm_num
  simp_rw [hcast]
  change
    (∑ n ∈ ((Finset.univ : Finset (Fin Q)).filter
        fun n => gamma n ≠ 0).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q)) = xi),
        ‖gamma n‖ ^ 2) =
      ∑ n ∈ (Finset.univ : Finset (Fin Q)).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q)) = xi),
        ‖gamma n‖ ^ 2
  apply Finset.sum_subset (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    exact hn.2)
  intro n hn hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn hnot
  have hnzero : gamma n = 0 := by
    by_contra hne
    exact hnot ⟨hne, hn⟩
  simp [hnzero]

/-- The monomial source phase agrees with the earlier literal box phase. -/
theorem wooleySourcePolynomialPhase_box_monomial
    {Q k q : ℕ} [NeZero q] (alpha : Fin k → ZMod q) (n : Fin Q) :
    wooleySourcePolynomialPhase (wooleyMonomialPolynomialSystem k) alpha
        (wooleyBoxIndexEmbedding Q n) =
      wooleyMonomialGridPhase q k Q alpha n := by
  unfold wooleySourcePolynomialPhase wooleyMonomialGridPhase
  apply congrArg ZMod.stdAddChar
  apply Finset.sum_congr rfl
  intro j hj
  simp [wooleyMonomialPolynomialSystem, wooleyBoxIndexEmbedding]

/-- The source phase agrees with the finite-box polynomial phase for every
integer polynomial system, not merely the monomial specialization. -/
theorem wooleySourcePolynomialPhase_box
    {Q k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (alpha : Fin k → ZMod q) (n : Fin Q) :
    wooleySourcePolynomialPhase phi alpha (wooleyBoxIndexEmbedding Q n) =
      wooleyPolynomialGridPhase phi q Q alpha n := by
  unfold wooleySourcePolynomialPhase wooleyPolynomialGridPhase
  apply congrArg ZMod.stdAddChar
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- General polynomial-system version of the source/box global-sum bridge. -/
theorem wooleySourcePolynomialSum_box
    {Q k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) :
    wooleySourcePolynomialSum phi (wooleyBoxSourceSequence gamma) alpha =
      wooleyPolynomialWeightedGridSum phi q gamma alpha := by
  rw [wooleySourcePolynomialSum, wooleyPolynomialWeightedGridSum,
    wooleyBoxSourceSequence_support, Finset.sum_map]
  simp only [wooleyBoxSourceSequence_apply_index,
    wooleySourcePolynomialPhase_box]
  apply Finset.sum_subset (by simp)
  intro n hn hnot
  have hnzero : gamma n = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_ne_iff] using hnot
  simp [hnzero]

/-- General polynomial-system version of the residue-sum bridge. -/
theorem wooleySourcePolynomialResidueSum_box
    {Q k q qH : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourcePolynomialResidueSum phi (wooleyBoxSourceSequence gamma)
        alpha xi =
      wooleyPolynomialWeightedResidueGridSum phi q gamma alpha xi := by
  unfold wooleySourcePolynomialResidueSum
    wooleyPolynomialWeightedResidueGridSum wooleyResidueClass
  rw [wooleyBoxSourceSequence_support]
  rw [Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_apply, wooleyBoxSourceSequence_apply_index,
    wooleySourcePolynomialPhase_box]
  simp only [wooleyBoxIndexEmbedding_apply]
  have hcast (n : Fin Q) :
      (((((n : ℕ) + 1 : ℕ) : ℤ) : ZMod qH)) =
        ((((n : ℕ) + 1 : ℕ) : ZMod qH)) := by norm_num
  simp_rw [hcast]
  change
    (∑ n ∈ ((Finset.univ : Finset (Fin Q)).filter
        fun n => gamma n ≠ 0).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)) = xi),
        gamma n * wooleyPolynomialGridPhase phi q Q alpha n) =
      ∑ n ∈ (Finset.univ : Finset (Fin Q)).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)) = xi),
        gamma n * wooleyPolynomialGridPhase phi q Q alpha n
  apply Finset.sum_subset (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    exact hn.2)
  intro n hn hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn hnot
  have hnzero : gamma n = 0 := by
    by_contra hne
    exact hnot ⟨hne, hn⟩
  simp [hnzero]

theorem wooleySourceNormalizedPolynomialSum_box
    {Q k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) :
    wooleySourceNormalizedPolynomialSum phi
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyPolynomialNormalizedGridSum phi q gamma alpha := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleyPolynomialNormalizedGridSum
  rw [wooleyBoxSourceSequence_massSq, wooleySourcePolynomialSum_box]

theorem wooleySourceNormalizedPolynomialResidueSum_box
    {Q k q qH : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourceNormalizedPolynomialResidueSum phi
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyPolynomialNormalizedResidueGridSum phi q gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleyPolynomialNormalizedResidueGridSum
  rw [wooleySourceResidueMassSq_box,
    wooleySourcePolynomialResidueSum_box]

/-- General polynomial-system source mean equals its finite-box realization. -/
theorem wooleySourcePolynomialMean_box
    {Q k q s : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : Fin Q → ℂ) :
    wooleySourcePolynomialMean s q phi (wooleyBoxSourceSequence gamma) =
      wooleyPolynomialWeightedGridMean phi s q gamma := by
  unfold wooleySourcePolynomialMean wooleyPolynomialWeightedGridMean
  simp_rw [wooleySourceNormalizedPolynomialSum_box]

/-- General polynomial-system conditioned source mean equals its finite-box
realization. -/
theorem wooleySourcePolynomialConditionedMean_box
    {Q k q qH s : ℕ} [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : Fin Q → ℂ) :
    wooleySourcePolynomialConditionedMean s q qH phi
        (wooleyBoxSourceSequence gamma) =
      wooleyPolynomialConditionedGridMean phi s q qH gamma := by
  unfold wooleySourcePolynomialConditionedMean
    wooleyPolynomialConditionedGridMean
  rw [wooleyBoxSourceSequence_massSq]
  split_ifs
  · rfl
  · simp_rw [wooleySourceResidueMassSq_box,
      wooleySourceNormalizedPolynomialResidueSum_box]

/-- The source global sum is literally the earlier box sum. -/
theorem wooleySourcePolynomialSum_box_monomial
    {Q k q : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) :
    wooleySourcePolynomialSum (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyWeightedGridSum q k gamma alpha := by
  rw [wooleySourcePolynomialSum, wooleyWeightedGridSum,
    wooleyBoxSourceSequence_support, Finset.sum_map]
  simp only [wooleyBoxSourceSequence_apply_index,
    wooleySourcePolynomialPhase_box_monomial]
  apply Finset.sum_subset (by simp)
  intro n hn hnot
  have hnzero : gamma n = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_ne_iff] using hnot
  simp [hnzero]

/-- Residue exponential sums agree under the box embedding. -/
theorem wooleySourcePolynomialResidueSum_box_monomial
    {Q k q qH : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
    wooleySourcePolynomialResidueSum (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyWeightedResidueGridSum q k gamma alpha xi := by
  unfold wooleySourcePolynomialResidueSum wooleyWeightedResidueGridSum
    wooleyResidueClass
  rw [wooleyBoxSourceSequence_support]
  rw [Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_apply, wooleyBoxSourceSequence_apply_index,
    wooleySourcePolynomialPhase_box_monomial]
  simp only [wooleyBoxIndexEmbedding_apply]
  have hcast (n : Fin Q) :
      (((((n : ℕ) + 1 : ℕ) : ℤ) : ZMod qH)) =
        ((((n : ℕ) + 1 : ℕ) : ZMod qH)) := by norm_num
  simp_rw [hcast]
  change
    (∑ n ∈ ((Finset.univ : Finset (Fin Q)).filter
        fun n => gamma n ≠ 0).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)) = xi),
        gamma n * wooleyMonomialGridPhase q k Q alpha n) =
      ∑ n ∈ (Finset.univ : Finset (Fin Q)).filter
        (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)) = xi),
        gamma n * wooleyMonomialGridPhase q k Q alpha n
  apply Finset.sum_subset (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    exact hn.2)
  intro n hn hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn hnot
  have hnzero : gamma n = 0 := by
    by_contra hne
    exact hnot ⟨hne, hn⟩
  simp [hnzero]

theorem wooleySourceNormalizedPolynomialSum_box_monomial
    {Q k q : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) :
      wooleySourceNormalizedPolynomialSum
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha =
      wooleyWeightedNormalizedGridSum q k gamma alpha := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleyWeightedNormalizedGridSum
  rw [wooleyBoxSourceSequence_massSq,
    wooleySourcePolynomialSum_box_monomial]

theorem wooleySourceNormalizedPolynomialResidueSum_box_monomial
    {Q k q qH : ℕ} [NeZero q] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) :
      wooleySourceNormalizedPolynomialResidueSum
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) alpha xi =
      wooleyWeightedNormalizedResidueGridSum q k gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleyWeightedNormalizedResidueGridSum
  rw [wooleySourceResidueMassSq_box,
    wooleySourcePolynomialResidueSum_box_monomial]

/-- The source global mean recovers the finite box polynomial mean. -/
theorem wooleySourcePolynomialMean_box_monomial
    {Q k q s : ℕ} [NeZero q] (gamma : Fin Q → ℂ) :
      wooleySourcePolynomialMean s q (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) =
      wooleyWeightedGridMean s k q gamma := by
  unfold wooleySourcePolynomialMean wooleyWeightedGridMean
  simp_rw [wooleySourceNormalizedPolynomialSum_box_monomial]

/-- The source conditioned mean recovers the finite box conditioned mean. -/
theorem wooleySourcePolynomialConditionedMean_box_monomial
    {Q k q qH s : ℕ} [NeZero q] [NeZero qH]
    (gamma : Fin Q → ℂ) :
      wooleySourcePolynomialConditionedMean s q qH
        (wooleyMonomialPolynomialSystem k)
        (wooleyBoxSourceSequence gamma) =
      wooleyWeightedConditionedGridMean s k q qH gamma := by
  unfold wooleySourcePolynomialConditionedMean
    wooleyWeightedConditionedGridMean
  rw [wooleyBoxSourceSequence_massSq]
  split_ifs
  · rfl
  · simp_rw [wooleySourceResidueMassSq_box,
      wooleySourceNormalizedPolynomialResidueSum_box_monomial]

#print axioms wooleyBoxSourceSequence_apply_index
#print axioms wooleyBoxSourceSequence_support
#print axioms wooleyBoxSourceSequence_massSq
#print axioms wooleySourcePolynomialPhase_box_monomial
#print axioms wooleySourcePolynomialPhase_box
#print axioms wooleySourcePolynomialSum_box
#print axioms wooleySourcePolynomialResidueSum_box
#print axioms wooleySourceNormalizedPolynomialSum_box
#print axioms wooleySourceNormalizedPolynomialResidueSum_box
#print axioms wooleySourcePolynomialMean_box
#print axioms wooleySourcePolynomialConditionedMean_box
#print axioms wooleySourcePolynomialSum_box_monomial
#print axioms wooleySourceResidueMassSq_box
#print axioms wooleySourcePolynomialResidueSum_box_monomial
#print axioms wooleySourceNormalizedPolynomialSum_box_monomial
#print axioms wooleySourceNormalizedPolynomialResidueSum_box_monomial
#print axioms wooleySourcePolynomialMean_box_monomial
#print axioms wooleySourcePolynomialConditionedMean_box_monomial

end

end GafniTao
