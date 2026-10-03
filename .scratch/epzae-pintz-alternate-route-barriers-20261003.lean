import TaoTrudgianYang2025.LiteratureDensity
import TaoTrudgianYang2025.HeathBrownPairSecants

/-! Limitations of two alternate endpoint proof routes.
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

end PintzAlternateRouteBarriers
