import TaoTrudgianYang2025.BourgainMassDichotomy
import TaoTrudgianYang2025.BourgainBandShift
import TaoTrudgianYang2025.BourgainBandCorrelation

/-!
# The actual-pattern zeta-band alternative

The existing retained-pattern dichotomy supplies W and a genuine heavy
difference level. The large branch now consumes that same level, selects
an actual zeta band, controls its measure, and finds a real shift hitting
it. The full subdivided Bourgain dichotomy remains a separate obligation.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- A genuine zeta-amplitude band and shifted integer slice in the large
branch of the retained-pattern alternative. Both dyadic losses and the
physical spatial enlargement remain explicit. W is chosen before alpha. -/
theorem bourgain_retained_zeta_band_dichotomy {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          ∀ α : ℝ,
            (P.ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 W.card+1),
              let D := bourgainDifferenceLevel W j
              let H := P.N^(ε/8)
              let U := P.T+H+1
              let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
              let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
              let J := bourgainZetaBandCount B U a
              D.Nonempty ∧ 2^j ≤ W.card ∧ 2^j*D.card ≤ 2*W.card^2 ∧
              ∃ q ∈ Finset.range J,
                let V := a*(2 : ℝ)^q
                let K := 2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
                let r := bourgainZetaBandCorrelation D H U V
                0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
                0 < volume.real (bourgainZetaBand U V) ∧
                P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                  K*bourgainZetaBandMass D H U V ∧
                V^4*volume.real (bourgainZetaBand U V) ≤ C*U^(1+ε) ∧
                bourgainZetaBandMass D H U V ≤ 2*H*(D.card : ℝ) ∧
                bourgainZetaBandMass D H U V ≤
                  (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand U V) ∧
                0 < r ∧
                bourgainZetaBandMass D H U V =
                  r*Real.sqrt (volume.real (bourgainZetaBand U V))*Real.sqrt (D.card : ℝ) ∧
                r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) ∧
                r^2*volume.real (bourgainZetaBand U V) ≤ 4*H^2*(D.card : ℝ) ∧
                r^2*(D.card : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)^2*volume.real (bourgainZetaBand U V) ∧
                ∃ u ∈ Set.Ioc (-H) H,
                  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
                  P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                    K*(2*H)*((D.filter fun ℓ : ℤ =>
                      (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ) := by
  obtain ⟨C₀, δ, hC₀, hδ, hpattern⟩ :=
    bourgain_retained_difference_level_dichotomy (τ := τ) hσ hε
  obtain ⟨B, C₁, T₀, hB, hC₁, hT₀, hband⟩ := bourgainZetaBand_positive_selection hε
  let C := max C₀ (max C₁ T₀)
  have hCC₀ : C₀ ≤ C := le_max_left _ _
  have hCC₁ : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : T₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, C, δ, hB, hC₀.trans hCC₀, hδ, ?_⟩
  intro P hN hNT hTu hVl
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨W, hsub, hsep, hbase, hpack, halt⟩ :=
    hpattern P (hCC₀.trans hN) hNT hTu hVl
  refine ⟨W, hsub, hsep, hbase, hpack.trans (by gcongr), ?_⟩
  intro α
  rcases halt α with hsmall | ⟨j, hj, hD, hpow, hsize, hlarge, hlevel⟩
  · left
    exact hsmall.trans (by gcongr)
  · right
    let D := bourgainDifferenceLevel W j
    let H := P.N^(ε/8)
    let U := P.T+H+1
    let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
    have hH : 0 < H := Real.rpow_pos_of_pos (zero_lt_one.trans P.one_lt_N) _
    have hU : T₀ ≤ U := by dsimp only [U]; linarith
    have hUp : 0 < U := by linarith
    have hrange : ∀ ℓ ∈ D, -U+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ U-H := by
      intro ℓ hℓ
      have hb := bourgainDifferenceSupport_bounds hbase (Finset.mem_filter.mp hℓ).1
      dsimp only [U]
      constructor <;> linarith [hb.1, hb.2]
    have hM : 0 < bourgainZetaDifferenceMoment W H :=
      lt_of_le_of_lt (by positivity) hlarge
    have hL : 0 < L := by
      by_contra h
      have hn := mul_nonpos_of_nonneg_of_nonpos
        (by positivity : (0 : ℝ) ≤ (Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1))
        (le_of_not_gt h)
      have hh : bourgainZetaDifferenceMoment W H ≤
          (Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*L := hlevel
      linarith
    let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
    let J := bourgainZetaBandCount B U a
    obtain ⟨q, hq, ha, hV, hmass, hmeasure, hLbound, hfourth, hcard, hoverlap⟩ :=
      hband D H U hH hU hrange hL
    let V := a*(2 : ℝ)^q
    let K := 2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hbound : P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
        K*bourgainZetaBandMass D H U V := by
      apply hlarge.trans_le
      apply hlevel.trans
      have hh := mul_le_mul_of_nonneg_left hLbound
        (by positivity : (0 : ℝ) ≤ (Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1))
      convert hh using 1
      dsimp only [K]
      ring
    obtain ⟨hr, _, _, hidentity, hrbound, hrmeasure, hrsize⟩ :=
      bourgainZetaBandCorrelation_bounds D hH hmass
    obtain ⟨u, hu, hslice, hshift⟩ := bourgainZetaBandMass_common_shift D hH hmass
    refine ⟨j, hj, hD, hpow, hsize, q, hq, hL, ha, hV, hmass, hmeasure,
      hbound, hfourth.trans (by gcongr), hcard, hoverlap, hr, hidentity, hrbound, hrmeasure, hrsize, u, hu, hslice, ?_⟩
    have hh : K*bourgainZetaBandMass D H U V ≤
        K*(2*H*((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hshift hK
    change P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
      K*(2*H)*((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ)
    exact hbound.trans_le (hh.trans_eq (mul_assoc _ _ _).symm)

end TaoTrudgianYang2025
