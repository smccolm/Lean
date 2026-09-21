import TaoTrudgianYang2025.AtkinsonHeightCover

/-!
# Actual half-width point clusters and separated center colors

The bins use their left endpoints as centers, so every occupied center stays
in the original closed height interval, including its terminal endpoint.
Both parity classes are kept; cardinality is recovered with every occupancy.
-/

noncomputable section

open Finset RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def pointClusterBins (H G : ℝ) (W : Finset ℝ) : Finset ℕ :=
  W.image (atkinsonHeightBin H (G/2))

def pointCluster (H G : ℝ) (W : Finset ℝ) (n : ℕ) : Finset ℝ :=
  atkinsonHeightFiber H (G/2) W n

def pointClusterCenter (H G : ℝ) (n : ℕ) : ℝ :=
  H+(n:ℝ)*(G/2)

def pointClusterCenters (H G : ℝ) (U : Finset ℕ) : Finset ℝ :=
  U.image (pointClusterCenter H G)

theorem pointCluster_subset (H G : ℝ) (W : Finset ℝ) (n : ℕ) :
    pointCluster H G W n ⊆ W :=
  atkinsonHeightFiber_subset H (G/2) W n

theorem mem_pointClusterBins_iff {H G : ℝ} {W : Finset ℝ} {n : ℕ} :
    n ∈ pointClusterBins H G W ↔ (pointCluster H G W n).Nonempty := by
  simp only [pointClusterBins, pointCluster, atkinsonHeightFiber,
    Finset.mem_image, Finset.Nonempty, Finset.mem_filter]

theorem pointCluster_card_partition (H G : ℝ) (W : Finset ℝ) :
    W.card = ∑ n ∈ pointClusterBins H G W, (pointCluster H G W n).card := by
  exact Finset.card_eq_sum_card_image (atkinsonHeightBin H (G/2)) W

theorem pointCluster_interval {H G : ℝ} {W : Finset ℝ} (n : ℕ)
    (hG : 0 < G) (hlow : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ pointCluster H G W n,
      pointClusterCenter H G n ≤ t ∧
        t ≤ pointClusterCenter H G n+G/2 :=
  atkinsonHeightFiber_interval n (half_pos hG) hlow

theorem pointCluster_symmetric_interval {H G : ℝ} {W : Finset ℝ} (n : ℕ)
    (hG : 0 < G) (hlow : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ pointCluster H G W n,
      pointClusterCenter H G n-G/2 ≤ t ∧
        t ≤ pointClusterCenter H G n+G/2 := by
  intro t ht
  have hi := pointCluster_interval n hG hlow t ht
  exact ⟨by linarith [hi.1],hi.2⟩

theorem pointClusterCenter_range {H G : ℝ} {W : Finset ℝ} {n : ℕ}
    (hG : 0 < G) (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hn : n ∈ pointClusterBins H G W) :
    H ≤ pointClusterCenter H G n ∧ pointClusterCenter H G n ≤ 2*H := by
  obtain ⟨t,ht⟩ := mem_pointClusterBins_iff.mp hn
  have htW := pointCluster_subset H G W n ht
  have hi := pointCluster_interval n hG (fun t ht => (hrange t ht).1) t ht
  constructor
  · unfold pointClusterCenter
    exact le_add_of_nonneg_right (by positivity)
  · exact hi.1.trans (hrange t htW).2

theorem pointClusterCenter_injective {H G : ℝ} (hG : 0 < G) :
    Function.Injective (pointClusterCenter H G) := by
  intro k l h
  have hm : (k:ℝ)*(G/2) = (l:ℝ)*(G/2) := by
    simpa only [pointClusterCenter, add_right_inj] using h
  have he : (k:ℝ) = (l:ℝ) :=
    mul_right_cancel₀ (ne_of_gt (half_pos hG)) hm
  exact_mod_cast he

theorem pointClusterCenters_card {H G : ℝ} (hG : 0 < G) (U : Finset ℕ) :
    (pointClusterCenters H G U).card = U.card :=
  Finset.card_image_of_injective U (pointClusterCenter_injective hG)

theorem pointClusterCenter_gap_of_same_parity {H G : ℝ} {k l : ℕ}
    (hG : 0 < G) (hkl : k < l) (hmod : k%2 = l%2) :
    G ≤ pointClusterCenter H G l-pointClusterCenter H G k := by
  have hk : k+2 ≤ l := by omega
  have hr : (k:ℝ)+2 ≤ (l:ℝ) := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hr hG.le
  unfold pointClusterCenter
  nlinarith

theorem pointClusterCenters_separated {H G : ℝ} (hG : 0 < G)
    (U : Finset ℕ) (e : ℕ) (hmod : ∀ n ∈ U, n%2 = e) :
    IsSeparated G (pointClusterCenters H G U) := by
  intro x hx y hy hxy
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
  have hne : k ≠ l := by intro h; subst l; exact hxy rfl
  have he : k%2 = l%2 := (hmod k hk).trans (hmod l hl).symm
  rw [Real.dist_eq]
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · rw [abs_sub_comm]
    exact (pointClusterCenter_gap_of_same_parity hG hkl he).trans (le_abs_self _)
  · exact (pointClusterCenter_gap_of_same_parity hG hlk he.symm).trans (le_abs_self _)

theorem card_eq_sum_parity_cards (U : Finset ℕ) :
    U.card = (U.filter (fun n => n%2 = 0)).card +
      (U.filter (fun n => n%2 = 1)).card := by
  have he : U.filter (fun n => ¬n%2 = 0) = U.filter (fun n => n%2 = 1) := by
    ext n
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    omega
  have h := Finset.card_filter_add_card_filter_not (s := U) (p := fun n => n%2 = 0)
  rw [he] at h
  exact h.symm

end TaoTrudgianYang2025
