import TaoTrudgianYang2025.BourgainSharedGrid
import TaoTrudgianYang2025.LargeValueSubdivision

/-!
# Pulling retained subfamilies back to the actual source ordinates

Local reflection uses a different origin in each component. The inverse
reflection returns real source subsets, preserving cardinality, separation
and every ordered integer difference count.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Inverse reflection of a retained normalized subfamily. -/
def LargeValuePattern.retainedOriginal (P : LargeValuePattern) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun t => P.intervalRight-t)

theorem LargeValuePattern.retainedOriginal_card (P : LargeValuePattern) (W : Finset ℝ) :
    (P.retainedOriginal W).card = W.card := by
  apply Finset.card_image_of_injective
  intro x y h
  linarith

theorem LargeValuePattern.retainedOriginal_subset (P : LargeValuePattern)
    {W : Finset ℝ} (hW : W ⊆ P.reflectedOrdinates) :
    P.retainedOriginal W ⊆ P.ordinates := by
  intro t ht
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp ht
  obtain ⟨v, hv, href⟩ := Finset.mem_image.mp (hW hw)
  have he : t = v := by linarith
  exact he ▸ hv

theorem LargeValuePattern.retainedOriginal_isSeparated (P : LargeValuePattern)
    {W : Finset ℝ} {δ : ℝ} (hsep : IsSeparated δ W) :
    IsSeparated δ (P.retainedOriginal W) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have huv : u ≠ v := by intro h; apply hxy; rw [h]
  have hs := hsep u hu v hv huv
  rw [Real.dist_eq] at hs ⊢
  have he : P.intervalRight-u-(P.intervalRight-v) = -(u-v) := by ring
  rw [he, abs_neg]
  exact hs

/-- The inverse image retains the original coefficient polynomial and sign. -/
theorem LargeValuePattern.retainedOriginal_large (P : LargeValuePattern)
    {W : Finset ℝ} (hW : W ⊆ P.reflectedOrdinates) :
    ∀ t ∈ P.retainedOriginal W,
      P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ := by
  intro t ht
  exact P.large t (P.retainedOriginal_subset hW ht)

/-- Reflection preserves each actual ordered difference count by also
swapping the two entries. The integer bin and its strict boundary are unchanged. -/
theorem bourgainDifferenceCount_reflected (W : Finset ℝ) (c : ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount (W.image (fun t => c-t)) ℓ = bourgainDifferenceCount W ℓ := by
  classical
  symm
  unfold bourgainDifferenceCount
  apply Finset.card_bij (fun p _ => (c-p.2, c-p.1))
  · intro p hp
    obtain ⟨hpW, hnear⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpW
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p.2, hp₂, rfl⟩, Finset.mem_image.mpr ⟨p.1, hp₁, rfl⟩⟩, ?_⟩
    have he : (c-p.2)-(c-p.1)-(ℓ : ℝ) = p.1-p.2-(ℓ : ℝ) := by ring
    simpa only [he] using hnear
  · intro p hp q hq heq
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  · intro q hq
    obtain ⟨hqW, hnear⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqW
    obtain ⟨x, hx, hex⟩ := Finset.mem_image.mp hq₁
    obtain ⟨y, hy, hey⟩ := Finset.mem_image.mp hq₂
    refine ⟨(y,x), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hy,hx⟩, ?_⟩
      have he : y-x-(ℓ : ℝ) = q.1-q.2-(ℓ : ℝ) := by linarith
      simpa only [he] using hnear
    · exact Prod.ext hex hey

theorem LargeValuePattern.retainedOriginal_differenceCount
    (P : LargeValuePattern) (W : Finset ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount (P.retainedOriginal W) ℓ = bourgainDifferenceCount W ℓ :=
  bourgainDifferenceCount_reflected W P.intervalRight ℓ

/-- A retained local reflection is pulled back into its actual source bin,
with its original coefficient polynomial still witnessing the large values. -/
theorem LargeValuePattern.localized_retainedOriginal (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (j : ℕ) {W : Finset ℝ}
    (hW : W ⊆ (P.localized L hL j).reflectedOrdinates) (hsep : IsSeparated 2 W) :
    let S := (P.localized L hL j).retainedOriginal W
    S ⊆ P.localBin L j ∧ S ⊆ P.ordinates ∧ S.card = W.card ∧
    IsSeparated 2 S ∧
    (∀ ℓ : ℤ, bourgainDifferenceCount S ℓ = bourgainDifferenceCount W ℓ) ∧
    (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) := by
  have hs := (P.localized L hL j).retainedOriginal_subset hW
  exact ⟨hs, hs.trans (P.localBin_subset L j),
    (P.localized L hL j).retainedOriginal_card W,
    (P.localized L hL j).retainedOriginal_isSeparated hsep,
    (P.localized L hL j).retainedOriginal_differenceCount W,
    (P.localized L hL j).retainedOriginal_large hW⟩

/-- Original bins are disjoint, including exact endpoint ordinates. -/
theorem LargeValuePattern.localBin_disjoint (P : LargeValuePattern)
    (L : ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (P.localBin L i) (P.localBin L j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

/-- Pulled-back retained subsets in distinct actual components are disjoint.
A union of normalized reflected sets would not have this property. -/
theorem LargeValuePattern.localized_retainedOriginal_disjoint (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) {i j : ℕ} (hij : i ≠ j) {W Z : Finset ℝ}
    (hW : W ⊆ (P.localized L hL i).reflectedOrdinates)
    (hZ : Z ⊆ (P.localized L hL j).reflectedOrdinates) :
    Disjoint ((P.localized L hL i).retainedOriginal W)
      ((P.localized L hL j).retainedOriginal Z) :=
  (P.localBin_disjoint L hij).mono
    ((P.localized L hL i).retainedOriginal_subset hW)
    ((P.localized L hL j).retainedOriginal_subset hZ)

/-- A finite family of retained local reflections has an actual disjoint
source union, with exact cardinality and the original large-value polynomial. -/
theorem LargeValuePattern.localized_retainedOriginal_union (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (A : Finset ℕ) (W : ℕ → Finset ℝ)
    (hW : ∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) :
    let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
    S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧ IsSeparated 1 S ∧
    (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) := by
  classical
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hsub : S ⊆ P.ordinates := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := Finset.mem_biUnion.mp ht
    exact P.localBin_subset L i ((P.localized L hL i).retainedOriginal_subset (hW i hi) ht)
  have hdis : (A : Set ℕ).PairwiseDisjoint
      (fun i => (P.localized L hL i).retainedOriginal (W i)) := by
    intro i hi j hj hij
    exact P.localized_retainedOriginal_disjoint hL hij (hW i hi) (hW j hj)
  refine ⟨hsub, ?_, ?_, fun t ht => P.large t (hsub ht)⟩
  · rw [Finset.card_biUnion hdis]
    apply Finset.sum_congr rfl
    intro i hi
    exact (P.localized L hL i).retainedOriginal_card (W i)
  · intro t ht u hu htu
    simpa only [Real.dist_eq] using P.ordinates_oneSeparated t (hsub ht) u (hsub hu) htu

end TaoTrudgianYang2025
