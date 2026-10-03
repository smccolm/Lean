import TaoTrudgianYang2025.LiteratureDensity
import TaoTrudgianYang2025.HeathBrownPairSecants
import TaoTrudgianYang2025.HeathBrownNineBranches
import TaoTrudgianYang2025.JutilaEnergyRegions

/-! Limitations of alternate endpoint proof routes.
These are scalar majorant statements, NOT counterexamples to the actual
density bounds, exponent-pair bounds, or zeta-function statements. -/

noncomputable section
namespace PintzAlternateRouteBarriers
open TaoTrudgianYang2025

/-- Every direct integer Heath--Brown pair has the same plateau obstruction.
The proof uses the existing global ordering of secants, not finite search. -/
theorem heathBrown_pair_plateau_all_orders {n r : ℕ}
    (hn : 4 ≤ n) (hr : 3 ≤ r) {τ : ℝ}
    (hτ : (n:ℝ)-2+2/(n:ℝ) ≤ τ) :
    1-1/((n:ℝ)*((n:ℝ)-1)) ≤
      heathBrownPairK r*τ+heathBrownPairL r-heathBrownPairK r := by
  have hn3 : 3 ≤ n := by omega
  have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hrr : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hn0 : (0:ℝ) < n := by linarith only [hnr]
  have hleft : heathBrownPairLeft n = (n:ℝ)-2+2/(n:ℝ) := by
    unfold heathBrownPairLeft
    field_simp
    ring
  have htwo : 2/(n:ℝ) ≤ 1 := (div_le_iff₀ hn0).mpr (by linarith only [hnr])
  have hsegment : heathBrownPairLeft n ≤ heathBrownPairRight n := by
    apply le_trans _ (heathBrownPairRight_lower hnr)
    rw [hleft]
    linarith only [htwo]
  have hbase := heathBrownPairSecant_segment_le (j:=n) (k:=r) hn3 hr
    (τ:=heathBrownPairLeft n) le_rfl hsegment
  rw [heathBrownPairSecant_left hnr] at hbase
  have hp := heathBrownPairK_pos hrr
  have hmono := mul_le_mul_of_nonneg_left
    (show heathBrownPairLeft n ≤ τ by rwa [hleft]) hp.le
  have hid := heathBrownPairIntercept_eq hrr
  unfold heathBrownPairSecant at hbase
  rw [hid] at hbase
  simp only [neg_div] at hbase
  linarith only [hbase,hmono]

/-- The first two branches of the retained-twelfth comparison alone permit
these cardinalities for every subdivision parameter. Thus merely optimizing
that parameter cannot yield a smaller bound in this tall-height range. -/
theorem twelfth_comparison_low_cardinality_feasible {σ τ ρ χ : ℝ}
    (hρ : ρ ≤ τ+3-5*σ) :
    2*ρ ≤ χ+max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ) := by
  have h₁ := le_max_left (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ)
  have h₂ := le_max_right (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ)
  linarith only [hρ,h₁,h₂]

/-- Explicit scalar feasibility at the first missing endpoint and its
required cutoff; this is not an assertion that an actual pattern attains rho. -/
theorem twelfth_first_endpoint_scalar_obstruction :
    3*(1-(39/40:ℝ)) < 1/10 ∧
    ∀ χ : ℝ, 2*(1/10:ℝ) ≤ χ+
      max (2-2*(39/40)+1/10) (2*(63/16-χ)+4-8*(39/40)+1/10) := by
  refine ⟨by norm_num, fun χ => ?_⟩
  exact twelfth_comparison_low_cardinality_feasible (by norm_num)

example {n r : ℕ} (hn : 4 ≤ n) (hr : 3 ≤ r) {τ : ℝ}
    (hτ : (n:ℝ)-2+2/(n:ℝ) ≤ τ) :
    1-1/((n:ℝ)*((n:ℝ)-1)) ≤
      heathBrownPairK r*τ+heathBrownPairL r-heathBrownPairK r :=
  heathBrown_pair_plateau_all_orders hn hr hτ

example {r : ℕ} (hr : 3 ≤ r) :
    (19/20:ℝ) ≤ heathBrownPairK r*(15/4)+heathBrownPairL r-heathBrownPairK r := by
  have hh := heathBrown_pair_plateau_all_orders (n:=5) (by omega) hr
    (τ:=15/4) (by norm_num)
  norm_num at hh
  exact hh

example {r : ℕ} (hr : 3 ≤ r) :
    (41/42:ℝ) ≤ heathBrownPairK r*(16/3)+heathBrownPairL r-heathBrownPairK r := by
  have hh := heathBrown_pair_plateau_all_orders (n:=7) (by omega) hr
    (τ:=16/3) (by norm_num)
  norm_num at hh
  exact hh

example {σ τ ρ χ : ℝ} (hρ : ρ ≤ τ+3-5*σ) :
    2*ρ ≤ χ+max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ) :=
  twelfth_comparison_low_cardinality_feasible hρ

example :
    3*(1-(39/40:ℝ)) < 1/10 ∧
    ∀ χ : ℝ, 2*(1/10:ℝ) ≤ χ+
      max (2-2*(39/40)+1/10) (2*(63/16-χ)+4-8*(39/40)+1/10) :=
  twelfth_first_endpoint_scalar_obstruction

#print axioms heathBrown_pair_plateau_all_orders
#print axioms twelfth_comparison_low_cardinality_feasible
#print axioms twelfth_first_endpoint_scalar_obstruction

/-- A proved fallback at the first disputed point, strictly weaker than the
printed 16/21. It does not alter the accepted source contract. -/
theorem proved_first_endpoint_fallback :
    TaoTrudgianYang2025.zeroDensityExponent (39/40) ≤ ((172304/199529:ℝ):EReal) := by
  have hh := zeroDensityExponent_le_bourgain_piece_8
    (σ:=39/40) (by norm_num) (by norm_num)
  norm_num [bourgainPieceEight,generatedBourgainPiece8,RationalAffineFraction.eval] at hh ⊢
  exact hh

/-- The preceding Pintz row is valid at the second disputed point. -/
theorem proved_second_endpoint_fallback :
    TaoTrudgianYang2025.zeroDensityExponent (41/42) ≤ ((28/37:ℝ):EReal) := by
  have hh := zeroDensityExponent_le_pintz_second_interior
    (σ:=41/42) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

/-- Every tail lower endpoint has an actual bound from its preceding
closed-upper source cell; it is not the stronger printed new-cell bound. -/
theorem proved_tail_endpoint_fallback {n : ℕ} (hn : 6 ≤ n) :
    TaoTrudgianYang2025.zeroDensityExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) ≤
      ((3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2):ℝ):EReal) := by
  by_cases hn6 : n = 6
  · subst n
    have hh := zeroDensityExponent_le_pintz_third_interior
      (σ:=59/60) (by norm_num) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have hn7 : 7 ≤ n := by omega
  have hnr : (7:ℝ) ≤ n := by exact_mod_cast hn7
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : (0:ℝ) < (n:ℝ)-1 := by linarith only [hnr]
  have hm : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hDm : 0 < 2*((n:ℝ)-1)*((n:ℝ)-2) :=
    mul_pos (by positivity) (by linarith only [hnr])
  have hDlt : 2*((n:ℝ)-1)*((n:ℝ)-2) < 2*(n:ℝ)*((n:ℝ)-1) := by
    nlinarith only [hnr]
  have hi := one_div_lt_one_div_of_lt hDm hDlt
  have hleft : 1-1/(2*((n-1:ℕ):ℝ)*(((n-1:ℕ):ℝ)-1)) <
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) := by
    rw [hm,show (n:ℝ)-1-1 = (n:ℝ)-2 by ring]
    exact sub_lt_sub_left hi 1
  have hright : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤
      1-1/(2*((n-1:ℕ):ℝ)*(((n-1:ℕ):ℝ)+1)) := by
    rw [hm,show 2*((n:ℝ)-1)*((n:ℝ)-1+1) = 2*(n:ℝ)*((n:ℝ)-1) by ring]
  have hh := zeroDensityExponent_le_pintz_tail_interior (by omega : 6 ≤ n-1)
    hleft hright
  rw [hm] at hh
  have hpoly : 0 < (n:ℝ)^2-2*(n:ℝ)+2 := by
    nlinarith only [sq_nonneg ((n:ℝ)-1)]
  have he : 3/(((n:ℝ)-1)*(1-2*((n:ℝ)-1-1)*
      (1-(1-1/(2*(n:ℝ)*((n:ℝ)-1)))))) =
      3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2) := by
    field_simp
    ring
  simpa only [he] using hh

example :
    TaoTrudgianYang2025.zeroDensityExponent (39/40) ≤ ((172304/199529:ℝ):EReal) :=
  proved_first_endpoint_fallback

example :
    TaoTrudgianYang2025.zeroDensityExponent (41/42) ≤ ((28/37:ℝ):EReal) :=
  proved_second_endpoint_fallback

example {n : ℕ} (hn : 6 ≤ n) :
    TaoTrudgianYang2025.zeroDensityExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) ≤
      ((3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2):ℝ):EReal) :=
  proved_tail_endpoint_fallback hn

example : TaoTrudgianYang2025.zeroDensityExponent (59/60) ≤ ((9/13:ℝ):EReal) := by
  have hh := proved_tail_endpoint_fallback (n:=6) (by omega)
  norm_num at hh
  exact hh

example : (16/21:ℝ) < 172304/199529 ∧ (63/85:ℝ) < 28/37 := by norm_num

#print axioms proved_first_endpoint_fallback
#print axioms proved_second_endpoint_fallback
#print axioms proved_tail_endpoint_fallback

/-- The fallback is strictly weaker than the printed new-cell value at
every tail lower endpoint; it cannot discharge that unchanged contract. -/
theorem tail_fallback_strictly_weaker {n : ℕ} (hn : 6 ≤ n) :
    3/((n:ℝ)-1) < 3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnm : 0 < (n:ℝ)-1 := by linarith only [hnr]
  have hpoly : 0 < (n:ℝ)^2-2*(n:ℝ)+2 := by
    nlinarith only [sq_nonneg ((n:ℝ)-1)]
  apply (div_lt_div_iff₀ hnm hpoly).mpr
  nlinarith only [hnr]

example {n : ℕ} (hn : 6 ≤ n) :
    3/((n:ℝ)-1) < 3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2) :=
  tail_fallback_strictly_weaker hn

#print axioms tail_fallback_strictly_weaker

end PintzAlternateRouteBarriers

namespace PintzAlternateRouteBarriers
open TaoTrudgianYang2025

/-- An algebraic ceiling for the eight branches of the classical moment
table. The seventh cutoff is enlarged to 57/62; this also covers its
printed cutoff 0.91591... . This is not a zeta moment theorem. -/
theorem classical_moment_table_weight_ceiling {c p : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c < 1)
    (htable :
      (c ≤ 5/8 ∧ p ≤ 4/(3-4*c)) ∨
      (c ≤ 35/54 ∧ p ≤ 10/(5-6*c)) ∨
      (c ≤ 41/60 ∧ p ≤ 19/(6-6*c)) ∨
      (c ≤ 3/4 ∧ p ≤ 2112/(859-948*c)) ∨
      (c ≤ 5/6 ∧ p ≤ 12408/(4537-4890*c)) ∨
      (c ≤ 7/8 ∧ p ≤ 4324/(1031-1044*c)) ∨
      (c ≤ 57/62 ∧ p ≤ 98/(31-32*c)) ∨
      p ≤ (24*c-9)/((4*c-1)*(1-c))) :
    p*(1-c) ≤ 5 := by
  have hbound (a d : ℝ) (hd : 0 < d)
      (hcap : a*(1-c) ≤ 5*d) (hp : p ≤ a/d) : p*(1-c) ≤ 5 := by
    calc
      _ ≤ (a/d)*(1-c) := mul_le_mul_of_nonneg_right hp (by linarith only [hc1])
      _ = (a*(1-c))/d := by ring
      _ ≤ 5 := (div_le_iff₀ hd).mpr hcap
  rcases htable with ⟨h, hp⟩ | ⟨h, hp⟩ | ⟨h, hp⟩ | ⟨h, hp⟩ |
    ⟨h, hp⟩ | ⟨h, hp⟩ | ⟨h, hp⟩ | hp
  · exact hbound 4 (3-4*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 10 (5-6*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 19 (6-6*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 2112 (859-948*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 12408 (4537-4890*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 4324 (1031-1044*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound 98 (31-32*c) (by linarith only [h]) (by linarith only [h]) hp
  · exact hbound (24*c-9) ((4*c-1)*(1-c))
      (mul_pos (by linarith only [hc]) (by linarith only [hc1]))
      (by nlinarith only [sq_nonneg (1-c)]) hp

/-- A fixed positive loss prevents that moment-table majorant from
closing even the left boundary of the remaining second Pintz strip.
This does not exclude a stronger moment theorem or the density endpoint. -/
theorem classical_moment_table_second_strip_gap {c p τ : ℝ}
    (hp : 0 ≤ p) (hceiling : p*(1-c) ≤ 5) (hτ : 37/7 ≤ τ) :
    3*τ/170+229/1190 ≤ τ-p*(41/42-c) := by
  nlinarith only [hp,hceiling,hτ]

example {c p : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1)
    (htable :
      (c ≤ 5/8 ∧ p ≤ 4/(3-4*c)) ∨
      (c ≤ 35/54 ∧ p ≤ 10/(5-6*c)) ∨
      (c ≤ 41/60 ∧ p ≤ 19/(6-6*c)) ∨
      (c ≤ 3/4 ∧ p ≤ 2112/(859-948*c)) ∨
      (c ≤ 5/6 ∧ p ≤ 12408/(4537-4890*c)) ∨
      (c ≤ 7/8 ∧ p ≤ 4324/(1031-1044*c)) ∨
      (c ≤ 57/62 ∧ p ≤ 98/(31-32*c)) ∨
      p ≤ (24*c-9)/((4*c-1)*(1-c))) :
    p*(1-c) ≤ 5 := classical_moment_table_weight_ceiling hc hc1 htable

example {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) :
    ((24*c-9)/((4*c-1)*(1-c)))*(1-c) ≤ 5 :=
  classical_moment_table_weight_ceiling hc hc1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr le_rfl)))))))

example {c p τ : ℝ} (hp : 0 ≤ p) (hceiling : p*(1-c) ≤ 5)
    (hτ : 37/7 ≤ τ) :
    3*τ/170+229/1190 ≤ τ-p*(41/42-c) :=
  classical_moment_table_second_strip_gap hp hceiling hτ

example : (0:ℝ) < 229/1190 ∧ (5:ℝ) < (1-3/170)*(37/7) := by norm_num

#print axioms classical_moment_table_weight_ceiling
#print axioms classical_moment_table_second_strip_gap

/-- The mean-value/pointwise interpolation used for high moments still
loses a fixed power on this strip whenever its pointwise majorant reaches
the disputed amplitude. Both sides of the integer-power split are covered. -/
theorem pointwise_power_moment_second_strip_gap (k : ℕ) {β τ : ℝ}
    (hβ : 41/42 ≤ β) (hτ : 37/7 ≤ τ) :
    3*τ/170+1537/3570 ≤
      if k ≤ 5 then τ+(k:ℝ)-2*k*(41/42)
      else τ+2*((k:ℝ)-5)*β+5-2*k*(41/42) := by
  split_ifs with hk
  · have hkr : (k:ℝ) ≤ 5 := by exact_mod_cast hk
    nlinarith only [hkr,hτ]
  · have hkr : (5:ℝ) ≤ k := by exact_mod_cast (show 5 ≤ k by omega)
    have hh := mul_nonneg (sub_nonneg.mpr hkr) (sub_nonneg.mpr hβ)
    nlinarith only [hh,hτ]

example (k : ℕ) {β τ : ℝ} (hβ : 41/42 ≤ β) (hτ : 37/7 ≤ τ) :
    3*τ/170+1537/3570 ≤
      if k ≤ 5 then τ+(k:ℝ)-2*k*(41/42)
      else τ+2*((k:ℝ)-5)*β+5-2*k*(41/42) :=
  pointwise_power_moment_second_strip_gap k hβ hτ

example (k : ℕ) {r : ℕ} (hr : 3 ≤ r) {τ : ℝ} (hτ : 37/7 ≤ τ) :
    3*τ/170+1537/3570 ≤
      if k ≤ 5 then τ+(k:ℝ)-2*k*(41/42)
      else τ+2*((k:ℝ)-5)*(heathBrownPairK r*τ+heathBrownPairL r-heathBrownPairK r)
        +5-2*k*(41/42) := by
  apply pointwise_power_moment_second_strip_gap k _ hτ
  have hh := heathBrown_pair_plateau_all_orders (n:=7) (by omega) hr
    (τ:=τ) (by norm_num; exact hτ)
  norm_num at hh
  exact hh

-- Bellotti--Yang Lemma 4.1's relaxed pointwise exponent has the same limitation.
example {τ : ℝ} (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    (41/42:ℝ) ≤ 1-(1-3/τ)/τ^2 := by
  have ht : 0 < τ := by linarith only [hτ]
  have ht5 : 5 ≤ τ := by linarith only [hτ]
  have hsq : 25 ≤ τ^2 := by nlinarith only [ht5]
  have hcube := mul_nonneg ht.le (sub_nonneg.mpr hsq)
  have he : (1-3/τ)/τ^2 = (τ-3)/τ^3 := by field_simp
  rw [he]
  have hratio : (τ-3)/τ^3 ≤ 1/42 :=
    (div_le_iff₀ (pow_pos ht 3)).mpr (by nlinarith only [hcube,hτu])
  linarith only [hratio]

#print axioms pointwise_power_moment_second_strip_gap

/-- The minimal energy at cardinality exponent `4*(1-sigma)` satisfies
every positive integer-powered Heath--Brown inequality, using just its
diagonal terms. This is scalar feasibility, not an actual region witness. -/
theorem heathBrown_energy_diagonal_feasible {σ τ q : ℝ}
    (hσ : σ ≤ 1) (hq : 1 ≤ q) :
    8*(1-σ)/q ≤ heathBrownEnergyRHS σ (τ/q) (4*(1-σ)/q) (8*(1-σ)/q) := by
  have hqp : 0 < q := by linarith only [hq]
  have hr : 4*(1-σ)/q ≤ 4*(1-σ) := (div_le_iff₀ hqp).mpr
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hq)])
  have h₁ := (le_max_left (4*(1-σ)/q+1) (2*(4*(1-σ)/q))).trans
    (le_max_left _ (5/4*(4*(1-σ)/q)+(τ/q)/2))
  have h₂ := (le_max_left (8*(1-σ)/q+1) (4*(4*(1-σ)/q))).trans
    (le_max_left _ (3/4*(8*(1-σ)/q)+4*(1-σ)/q+(τ/q)/2))
  unfold heathBrownEnergyRHS
  rw [show 8*(1-σ)/q = 2*(4*(1-σ)/q) by ring] at h₂ ⊢
  nlinarith only [hr,h₁,h₂]

/-- All independent positive powers in the nine-branch elimination still
permit the same scalar tuple. The explicit witness is the first branch. -/
theorem heathBrown_nine_diagonal_feasible {σ τ q l : ℝ}
    (hσ : σ ≤ 1) (hq : 0 < q) (hl : 1 ≤ l) :
    ∃ i : Fin 9, 8*(1-σ)/q ≤
      heathBrownNineBranch σ (τ/q) (4*(1-σ)/q) (l/q) i := by
  refine ⟨0, ?_⟩
  change 8*(1-σ)/q ≤ (4-4*σ)*(l/q)+4*(1-σ)/q
  rw [show (4-4*σ)*(l/q)+4*(1-σ)/q = (4*(1-σ)*l+4*(1-σ))/q by ring]
  apply (div_le_div_iff_of_pos_right hq).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hl)]

/-- The same second-strip cardinality also satisfies every integer-powered
Jutila bound. Thus adding those constraints does not eliminate this tuple. -/
theorem jutila_second_strip_diagonal_feasible {τ : ℝ} (hτ : 37/7 ≤ τ)
    (q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k) :
    (2/21:ℝ)/q ≤ jutilaLargeValueExponent k (41/42) (τ/q) := by
  by_cases hq1 : q = 1
  · subst q
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (0:ℝ) < k := by linarith only [hkr]
    have hinv : 1/(k:ℝ) ≤ 1 := (div_le_one hkp).mpr hkr
    have hb := (le_max_left (τ+4-2/(k:ℝ)-(6-2/(k:ℝ))*(41/42))
      (τ+(6-8*(41/42))*(k:ℝ))).trans (le_max_right (2-2*(41/42)) _)
    have hf : (2/21:ℝ) ≤ τ+4-2/(k:ℝ)-(6-2/(k:ℝ))*(41/42) := by
      rw [show 2/(k:ℝ) = 2*(1/(k:ℝ)) by ring]
      nlinarith only [hτ,hinv]
    simpa only [jutilaLargeValueExponent,Nat.cast_one,div_one] using hf.trans hb
  · have hqr : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hqp : (0:ℝ) < q := by linarith only [hqr]
    apply le_trans _ (le_max_left _ _)
    apply (div_le_iff₀ hqp).mpr
    nlinarith only [hqr]

/-- At every point of the residual strip, rho=2/21 is too large for the
target but is consistent with the elementary energy/double-zeta bounds,
the double-zeta Heath--Brown majorant, and the absolute-value Gram/CS
exponent inequality. No realization by an actual pattern is asserted. -/
theorem second_strip_energy_scalar_feasible {τ : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    3*τ/170 < (2/21:ℝ) ∧
    0 ≤ (2/21:ℝ) ∧ (2/21:ℝ) ≤ τ ∧
    2*(2/21:ℝ) ≤ 4/21 ∧ (4/21:ℝ) ≤ 3*(2/21) ∧
    (2/21:ℝ)+2 ≤ 44/21 ∧ (44/21:ℝ) ≤ 2*(2/21)+2 ∧
    (44/21:ℝ) ≤ max (max (2/21+1) (2*(2/21))) (5/4*(2/21)+τ/2)+1 ∧
    2*(2/21:ℝ)+2*(41/42) ≤ 1+2/21+(44/21)/2 := by
  have hd := (le_max_left (2/21+1:ℝ) (2*(2/21))).trans
    (le_max_left _ (5/4*(2/21)+τ/2))
  refine ⟨by linarith only [hτu], by norm_num, by linarith only [hτ],
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  linarith only [hd]

example {σ τ q : ℝ} (hσ : σ ≤ 1) (hq : 1 ≤ q) :
    8*(1-σ)/q ≤ heathBrownEnergyRHS σ (τ/q) (4*(1-σ)/q) (8*(1-σ)/q) :=
  heathBrown_energy_diagonal_feasible hσ hq

example {σ τ q l : ℝ} (hσ : σ ≤ 1) (hq : 0 < q) (hl : 1 ≤ l) :
    ∃ i : Fin 9, 8*(1-σ)/q ≤
      heathBrownNineBranch σ (τ/q) (4*(1-σ)/q) (l/q) i :=
  heathBrown_nine_diagonal_feasible hσ hq hl

example {τ : ℝ} (hτ : 37/7 ≤ τ) (q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k) :
    (2/21:ℝ)/q ≤ jutilaLargeValueExponent k (41/42) (τ/q) :=
  jutila_second_strip_diagonal_feasible hτ q k hq hk

example {τ : ℝ} (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    3*τ/170 < (2/21:ℝ) ∧
    0 ≤ (2/21:ℝ) ∧ (2/21:ℝ) ≤ τ ∧
    2*(2/21:ℝ) ≤ 4/21 ∧ (4/21:ℝ) ≤ 3*(2/21) ∧
    (2/21:ℝ)+2 ≤ 44/21 ∧ (44/21:ℝ) ≤ 2*(2/21)+2 ∧
    (44/21:ℝ) ≤ max (max (2/21+1) (2*(2/21))) (5/4*(2/21)+τ/2)+1 ∧
    2*(2/21:ℝ)+2*(41/42) ≤ 1+2/21+(44/21)/2 :=
  second_strip_energy_scalar_feasible hτ hτu

-- These use the exact production RHS definitions, at every integer power.
example (q : ℕ) (hq : 1 ≤ q) (τ : ℝ) :
    (4/21:ℝ)/q ≤ heathBrownEnergyRHS (41/42) (τ/q) ((2/21)/q) ((4/21)/q) := by
  have hh := heathBrown_energy_diagonal_feasible (σ:=41/42) (τ:=τ)
    (q:=(q:ℝ)) (by norm_num) (by exact_mod_cast hq)
  norm_num at hh ⊢
  exact hh

example (q l : ℕ) (hq : 1 ≤ q) (hl : 1 ≤ l) (τ : ℝ) :
    ∃ i : Fin 9, (4/21:ℝ)/q ≤
      heathBrownNineBranch (41/42) (τ/q) ((2/21)/q) ((l:ℝ)/q) i := by
  have hh := heathBrown_nine_diagonal_feasible (σ:=41/42) (τ:=τ)
    (q:=(q:ℝ)) (l:=(l:ℝ)) (by norm_num)
    (by exact_mod_cast (show 0 < q by omega)) (by exact_mod_cast hl)
  norm_num at hh ⊢
  exact hh

example : (37/7:ℝ) ≤ 16/3 ∧ (16/3:ℝ) < 340/63 ∧
    3*(16/3:ℝ)/170 = 8/85 ∧ (2/21:ℝ)-8/85 = 2/1785 := by norm_num

-- Even the simplified small-height two-branch inequality permits the tuple.
example (q : ℕ) (hq : 1 ≤ q) :
    (4/21:ℝ)/q ≤ max ((2/21:ℝ)/q+4-4*(41/42))
      ((3-4*(41/42)+5*((2/21:ℝ)/q))/2) := by
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0:ℝ) < q := by linarith only [hqr]
  have hr : (2/21:ℝ)/q ≤ 2/21 := (div_le_iff₀ hqp).mpr
    (by linarith only [hqr])
  apply le_trans _ (le_max_left _ _)
  rw [show (4/21:ℝ)/q = 2*((2/21:ℝ)/q) by ring]
  linarith only [hr]

-- The displayed Bourgain estimator in Pintz--Revesz (2024), equations
-- (21),(24), has a 4*lambda_zeta(2*eta) term already larger than the target.
-- This says nothing about a stronger choice of growth estimator.
example : (26/21:ℝ)/(1-4*(1/42)) = 26/19 ∧ (63/85:ℝ) < 26/19 := by norm_num

#print axioms heathBrown_energy_diagonal_feasible
#print axioms heathBrown_nine_diagonal_feasible
#print axioms jutila_second_strip_diagonal_feasible
#print axioms second_strip_energy_scalar_feasible

end PintzAlternateRouteBarriers
