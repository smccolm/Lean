import TaoTrudgianYang2025.BourgainSmallMass

/-!
# The actual small-mass / heavy-difference-level alternative

The source pattern supplies the separated subfamily. Its genuine zeta
moment either gives the solved small-mass bound, or selects a nonempty
integer difference level with its exact logarithmic and cardinality costs.
The later zeta superlevel/common-shift argument is not assumed or claimed.
-/

open Finset RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

namespace TaoTrudgianYang2025

/-- The beginning of Bourgain's analytic dichotomy on actual patterns.
The free parameter alpha is chosen after the same subfamily W; the large
branch supplies an actual dyadic difference level, not an assumed selector. -/
theorem bourgain_retained_difference_level_dichotomy {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          ∀ α : ℝ,
            (P.ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 W.card+1),
              (bourgainDifferenceLevel W j).Nonempty ∧
              2^j ≤ W.card ∧
              2^j*(bourgainDifferenceLevel W j).card ≤ 2*W.card^2 ∧
              P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                bourgainZetaDifferenceMoment W (P.N^(ε/8)) ∧
              bourgainZetaDifferenceMoment W (P.N^(ε/8)) ≤
                (Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
                  ∑ ℓ ∈ bourgainDifferenceLevel W j,
                    bourgainLocalZetaSquare (P.N^(ε/8)) ℓ := by
  let ν := ε/8
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνe : ν ≤ ε := by dsimp [ν]; linarith
  have h4νe : 4*ν ≤ ε := by dsimp [ν]; linarith
  obtain ⟨C₀,δ,hC₀,hδ,hp⟩ := bourgain_retained_source_power_bound (τ := τ) hσ hν
  let C := max C₀ (2*C₀+16*C₀^4)
  have hC₀p : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hCC : C₀ ≤ C := le_max_left _ _
  have hC : 1 ≤ C := hC₀.trans hCC
  have h2C : 2*C₀ ≤ C := by
    have hh := le_max_right C₀ (2*C₀+16*C₀^4)
    have hp : 0 ≤ C₀^4 := by positivity
    dsimp [C]
    linarith
  have h16C : 16*C₀^4 ≤ C := by
    have hh := le_max_right C₀ (2*C₀+16*C₀^4)
    dsimp [C]
    linarith
  refine ⟨C,δ,hC,hδ,?_⟩
  intro P hN hNT hTu hVl
  have hN1 := P.one_lt_N.le
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨W,hsub,hsep,hbase,hcard,hbound⟩ := hp P (hCC.trans hN) hNT hTu hVl
  have hWcard : (W.card : ℝ) ≤ P.ordinates.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq P.reflectedOrdinates_card
  refine ⟨W,hsub,hsep,hbase,hcard.trans ?_,?_⟩
  · gcongr
  intro α
  let M := bourgainZetaDifferenceMoment W (P.N^ν)
  by_cases hsmall : M ≤ P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2)
  · left
    have hm : M ≤ P.N^(-α)*(P.ordinates.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) :=
      hsmall.trans (by gcongr)
    have hs := bourgain_small_mass_power_bound hNp (Nat.cast_nonneg P.ordinates.card)
      hC₀p.le hm hbound
    have h1 : P.N^(2-2*σ+ν) ≤ P.N^(2-2*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : P.N^(2*τ+4-8*σ+ν) ≤ P.N^(2*τ+4-8*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h3 : P.N^(-2*α+τ+12-16*σ+4*ν) ≤ P.N^(-2*α+τ+12-16*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc
      _ ≤ (2*C₀)*P.N^(2-2*σ+ν)+(2*C₀)*P.N^(2*τ+4-8*σ+ν)+
          (16*C₀^4)*P.N^(-2*α+τ+12-16*σ+4*ν) := hs
      _ ≤ C*P.N^(2-2*σ+ε)+C*P.N^(2*τ+4-8*σ+ε)+C*P.N^(-2*α+τ+12-16*σ+ε) := by gcongr
      _ = _ := by ring
  · right
    have hmass : 0 < M := lt_of_le_of_lt (by positivity) (lt_of_not_ge hsmall)
    obtain ⟨j,hj,hne,hpow,hsize,hm⟩ :=
      bourgainZetaDifferenceMoment_select_level hsep (by positivity) hmass
    exact ⟨j,hj,hne,hpow,hsize,lt_of_not_ge hsmall,hm⟩

end TaoTrudgianYang2025
