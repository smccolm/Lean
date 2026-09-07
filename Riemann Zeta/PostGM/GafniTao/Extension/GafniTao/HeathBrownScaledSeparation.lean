import RiemannZeta.GuthMaynard.ClassicalLargeValues

/-!
# Harmonic reciprocal mass at an arbitrary separation scale

Ivić's use of the Bombieri--Halász inequality keeps a physical spacing
parameter `G`.  The frozen Guth--Maynard library contains the corresponding
unit-spacing lemma.  Here we prove its literal scale-`G` form, including the
factor `G⁻¹`, without altering the frozen foundation.
-/

open Finset Real
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

private theorem separated_subset_card_le_one_of_diameter_scaled
    (G : ℝ) (W S : Finset ℝ) (hSep : IsSeparated G W) (hSW : S ⊆ W)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < G) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  have hlarge := hSep x (hSW hx) y (hSW hy) hxy
  exact (not_lt_of_ge hlarge) (by simpa [Real.dist_eq] using hdiam x hx y hy)

/-- An annulus of width `G` around `t` contains at most one `G`-separated
point on either side of `t`. -/
theorem separated_scaled_annulus_card_le_two
    (G : ℝ) (W : Finset ℝ) (t : ℝ) (k : ℕ)
    (hSep : IsSeparated G W) :
    ({u ∈ W | u ≠ t ∧ (k : ℝ) * G ≤ |u - t| ∧
      |u - t| < ((k : ℝ) + 1) * G}).card ≤ 2 := by
  let S := {u ∈ W | u ≠ t ∧ (k : ℝ) * G ≤ |u - t| ∧
    |u - t| < ((k : ℝ) + 1) * G}
  let P : ℝ → Prop := fun u => t ≤ u
  have hpos : (S.filter P).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter_scaled G W (S.filter P) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      rw [abs_of_nonneg (sub_nonneg.mpr hxData.2)] at hxS
      rw [abs_of_nonneg (sub_nonneg.mpr hyData.2)] at hyS
      rw [abs_lt]
      constructor <;> nlinarith [hxS.2.2, hyS.2.2]
  have hneg : (S.filter (fun u => ¬P u)).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter_scaled G W
      (S.filter (fun u => ¬P u)) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      have hxt : x - t ≤ 0 := by linarith
      have hyt : y - t ≤ 0 := by linarith
      rw [abs_of_nonpos hxt] at hxS
      rw [abs_of_nonpos hyt] at hyS
      rw [abs_lt]
      constructor <;> nlinarith [hxS.2.2, hyS.2.2]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) P
  change S.card ≤ 2
  omega

/-- Exact scale-`G` reciprocal-distance estimate on a radius `N * G`.
The factor `2` records the two sides of the centre. -/
theorem sum_inv_distance_scaled_near_le_harmonic
    (G : ℝ) (N : ℕ) (W : Finset ℝ) (t : ℝ)
    (hG : 0 < G) (hSep : IsSeparated G W) (ht : t ∈ W) :
    (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ) * G},
        1 / |u - t|) ≤
      (2 / G) * (((harmonic N : ℚ) : ℝ)) := by
  let S := {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ) * G}
  let shell : ℝ → ℕ := fun u => Nat.floor (|u - t| / G)
  have hmaps : ∀ u ∈ S, shell u ∈ Finset.Icc 1 N := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have hu := huData.1
    have hne := huData.2.1
    have hsep := hSep t ht u hu (Ne.symm hne)
    have hqOne : 1 ≤ |u - t| / G := by
      rw [Real.dist_eq, abs_sub_comm] at hsep
      exact (le_div_iff₀ hG).2 (by simpa using hsep)
    have hqNonneg : 0 ≤ |u - t| / G := div_nonneg (abs_nonneg _) hG.le
    have hfloorPos : 0 < shell u := Nat.floor_pos.mpr hqOne
    have hratioLe : |u - t| / G ≤ (N : ℝ) := by
      exact (div_le_iff₀ hG).2 huData.2.2
    have hfloorLeReal : ((shell u : ℕ) : ℝ) ≤ (N : ℝ) :=
      (Nat.floor_le hqNonneg).trans hratioLe
    have hfloorLe : shell u ≤ N := by exact_mod_cast hfloorLeReal
    exact Finset.mem_Icc.mpr ⟨hfloorPos, hfloorLe⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun u => 1 / |u - t|)]
  calc
    (∑ k ∈ Finset.Icc 1 N,
        ∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
        ∑ k ∈ Finset.Icc 1 N, 2 * (1 / ((k : ℝ) * G)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hkGPos : 0 < (k : ℝ) * G := mul_pos (by exact_mod_cast hkPos) hG
      have hfiberCard : ({u ∈ S | shell u = k}).card ≤ 2 := by
        calc
          ({u ∈ S | shell u = k}).card ≤
              ({u ∈ W | u ≠ t ∧ (k : ℝ) * G ≤ |u - t| ∧
                |u - t| < ((k : ℝ) + 1) * G}).card := by
            apply Finset.card_le_card
            intro u hu
            have huData := Finset.mem_filter.mp hu
            have huS := Finset.mem_filter.mp huData.1
            have hfloor := huData.2
            have hqNonneg : 0 ≤ |u - t| / G :=
              div_nonneg (abs_nonneg _) hG.le
            have hlowRatio : (k : ℝ) ≤ |u - t| / G := by
              rw [← hfloor]
              exact Nat.floor_le hqNonneg
            have hhighRatio : |u - t| / G < (k : ℝ) + 1 := by
              rw [← hfloor]
              exact Nat.lt_floor_add_one _
            have hlow : (k : ℝ) * G ≤ |u - t| :=
              (le_div_iff₀ hG).1 hlowRatio
            have hhigh : |u - t| < ((k : ℝ) + 1) * G :=
              (div_lt_iff₀ hG).1 hhighRatio
            exact Finset.mem_filter.mpr
              ⟨huS.1, huS.2.1, hlow, hhigh⟩
          _ ≤ 2 := separated_scaled_annulus_card_le_two G W t k hSep
      calc
        (∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
            ∑ u ∈ S with shell u = k, 1 / ((k : ℝ) * G) := by
          apply Finset.sum_le_sum
          intro u hu
          have huData := Finset.mem_filter.mp hu
          have hfloor := huData.2
          have hqNonneg : 0 ≤ |u - t| / G :=
            div_nonneg (abs_nonneg _) hG.le
          have hkqRatio : (k : ℝ) ≤ |u - t| / G := by
            rw [← hfloor]
            exact Nat.floor_le hqNonneg
          have hkq : (k : ℝ) * G ≤ |u - t| :=
            (le_div_iff₀ hG).1 hkqRatio
          exact one_div_le_one_div_of_le hkGPos hkq
        _ = (({u ∈ S | shell u = k}).card : ℝ) *
            (1 / ((k : ℝ) * G)) := by simp
        _ ≤ 2 * (1 / ((k : ℝ) * G)) := by
          gcongr
          exact_mod_cast hfiberCard
    _ = (2 / G) * (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [inv_eq_one_div]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
      field_simp


end

end GafniTao
