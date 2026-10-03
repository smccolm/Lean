import TaoTrudgianYang2025.BourgainRetainedPullback
import TaoTrudgianYang2025.BourgainMixedFamily
import TaoTrudgianYang2025.BourgainMixedUpper
import TaoTrudgianYang2025.BourgainPhysicalUpper
import TaoTrudgianYang2025.BourgainSliceSelection
import TaoTrudgianYang2025.BourgainBudgetLogarithm
import TaoTrudgianYang2025.BourgainLogPacking
import TaoTrudgianYang2025.ZetaTwelfthGlobal
import TaoTrudgianYang2025.BourgainSubdivisionScale
import TaoTrudgianYang2025.BourgainBandLogBounds
import TaoTrudgianYang2025.BourgainRegionRealization
import TaoTrudgianYang2025.ClassicalLargeValueRegions
import TaoTrudgianYang2025.LargeValueExponentAttainment
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
Focused scratch route for the remaining Bourgain literature row.
Remaining chain: actual localized retained recurrence -> common weighted band
and mixed comparison -> zero-loss bound -> exact density consumer.
The scalar budgets below are not themselves a large-values theorem.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace BourgainTwelfthLiteratureScratch
open TaoTrudgianYang2025

theorem retained_quadratic {R a b M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (h : R ≤ a+b*Real.sqrt M) :
    R^2 ≤ 2*a*R+b^2*M := by
  have hm := mul_le_mul_of_nonneg_right h hR
  have hs := sq_nonneg (R-b*Real.sqrt M)
  have he : (b*Real.sqrt M)^2 = b^2*M := by
    rw [mul_pow,Real.sq_sqrt hM]
  nlinarith only [hm,hs,he]

theorem localized_retained_quadratic {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card:ℝ) ≤ C*P.N^ε*((W i).card:ℝ)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          (∑ i ∈ I, ((P.localized L hL i).ordinates.card:ℝ)^2) ≤
            2*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            (C*P.N^(3-4*σ+ε))^2 *
              ∑ i ∈ I, bourgainZetaDifferenceMoment (W i) (P.N^ε) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := bourgain_retained_source_power_bound (τ:=τ) hσ hε
  refine ⟨C,δ,hC,hδ,?_⟩
  intro P L hL hN hNL hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hlocal (i : ℕ) := hbound (P.localized L hL i) hN hNL hTu hV
  choose W hsub hsep hbase hpack hrec using hlocal
  refine ⟨W,fun i => ⟨hsub i,hsep i,hbase i,hpack i⟩,?_⟩
  let I := Finset.range (Nat.floor (P.T/L)+1)
  have hquad (i : ℕ) :
      ((P.localized L hL i).ordinates.card:ℝ)^2 ≤
        2*(C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)))*
          ((P.localized L hL i).ordinates.card:ℝ)+
        (C*P.N^(3-4*σ+ε))^2*bourgainZetaDifferenceMoment (W i) (P.N^ε) := by
    apply retained_quadratic (Nat.cast_nonneg _)
      (bourgainZetaDifferenceMoment_nonneg _ (by positivity))
    have hh := hrec i
    change ((P.localized L hL i).ordinates.card:ℝ) ≤
      C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
        P.N^(3-4*σ+ε)*Real.sqrt (bourgainZetaDifferenceMoment (W i) (P.N^ε))) at hh
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ I) => hquad i)
  have hpartition : (∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)) =
      (P.ordinates.card:ℝ) := by
    exact_mod_cast (P.card_eq_sum_localized hL).symm
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hpartition] at hsum
  convert hsum using 1
  ring

theorem localized_square_mass (P : LargeValuePattern) {L : ℝ} (hL : 0 < L) :
    (P.ordinates.card:ℝ)^2 ≤
      ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ)*
        ∑ i ∈ Finset.range (Nat.floor (P.T/L)+1),
          ((P.localized L hL i).ordinates.card:ℝ)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range (Nat.floor (P.T/L)+1))
    (fun _ => (1:ℝ)) (fun i => ((P.localized L hL i).ordinates.card:ℝ))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  have he : (∑ i ∈ Finset.range (Nat.floor (P.T/L)+1),
      ((P.localized L hL i).ordinates.card:ℝ)) = (P.ordinates.card:ℝ) := by
    exact_mod_cast (P.card_eq_sum_localized hL).symm
  simpa only [he] using h

theorem zeta_twelfth_symmetric {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (∫ t in -T..T, zetaMomentCriticalNorm t^12) ≤ C*T^(2+ε) := by
  obtain ⟨C,T₀,hC,hT₀,hbound⟩ := zeta_twelfth_zero hε
  refine ⟨2*C,T₀,by positivity,hT₀,?_⟩
  intro T hT
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t => zetaMomentCriticalNorm t^12) volume a b :=
    (continuous_zetaMomentCriticalNorm.pow 12).intervalIntegrable a b
  have heven : (∫ t in -T..0,zetaMomentCriticalNorm t^12) =
      ∫ t in 0..T,zetaMomentCriticalNorm t^12 := by
    have hs := intervalIntegral.integral_comp_neg
      (fun t => zetaMomentCriticalNorm t^12) (a:=(0:ℝ)) (b:=T)
    simpa only [zetaMomentCriticalNorm_neg,neg_zero] using hs.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T),heven]
  have h := hbound T hT
  nlinarith

theorem zeta_band_twelfth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T V : ℝ, T₀ ≤ T → 0 ≤ V →
      V^12*volume.real (bourgainZetaBand T V) ≤ C*T^(2+ε) := by
  obtain ⟨C,T₀,hC,hT₀,hbound⟩ := zeta_twelfth_symmetric hε
  refine ⟨C,T₀,hC,hT₀,?_⟩
  intro T V hT hV
  have hi : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc (-T) T) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => V^12) (bourgainZetaBand T V) :=
    integrableOn_const (bourgainZetaBand_measure_lt_top T V).ne
  have hmass : V^12*volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T,zetaMomentCriticalNorm t^12 := by
    rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc]
    calc
      _ = ∫ _ in bourgainZetaBand T V,V^12 := by simp [mul_comm]
      _ ≤ ∫ t in bourgainZetaBand T V,zetaMomentCriticalNorm t^12 :=
        setIntegral_mono_on hc (hi.mono_set (bourgainZetaBand_subset_Icc T V))
          (measurableSet_bourgainZetaBand T V) (fun t ht =>
            pow_le_pow_left₀ hV ((mem_bourgainZetaBand T V t).mp ht).2.2.1 12)
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall (bourgainZetaBand_subset_Icc T V))
  exact hmass.trans (hbound T hT)

theorem candidate_budget {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) := by
  dsimp only
  have hσp : 0 < 2*σ := by linarith
  have h₁ : 2-2*σ+max 0 (τ+1-3*σ) ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    by_cases hc : τ+1-3*σ ≤ 0
    · rw [max_eq_left hc]
      have hp := mul_nonneg (by linarith : 0 ≤ 1-σ) (by linarith : 0 ≤ 3*τ-4*σ)
      nlinarith
    · rw [max_eq_right (by linarith : 0 ≤ τ+1-3*σ)]
      have hp := mul_nonneg (by linarith : 0 ≤ 5*σ-3) (by linarith : 0 ≤ 2*σ-τ)
      nlinarith
  have h₂ : 2*τ+4-8*σ-max 0 (τ+1-3*σ) ≤ 2-2*σ+max 0 (τ+1-3*σ) := by
    have hc := le_max_right 0 (τ+1-3*σ)
    linarith
  have h₃ : (40+2*τ-52*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 13*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 39*σ-31)
    nlinarith
  exact max_le h₁ (max_le (h₂.trans h₁) h₃)

theorem candidate_scale_budgets {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    0 ≤ χ ∧ 1 < τ-χ ∧ τ-χ < 24*σ-35/2 ∧ τ-χ < 12*σ-8 ∧
      max (2-2*σ) (τ+4-6*σ) ≤ min 1 (4-2*τ) := by
  dsimp only
  have hχ := le_max_left 0 (τ+1-3*σ)
  have hloc : τ-max 0 (τ+1-3*σ) ≤ 3*σ-1 := by
    have := le_max_right 0 (τ+1-3*σ)
    linarith
  have hmargin : 1 < τ-max 0 (τ+1-3*σ) := by
    by_cases hc : τ+1-3*σ ≤ 0
    · rw [max_eq_left hc]; linarith
    · rw [max_eq_right (by linarith : 0 ≤ τ+1-3*σ)]; linarith
  refine ⟨hχ,hmargin,by linarith,by linarith,?_⟩
  exact max_le (le_min (by linarith) (by linarith))
    (le_min (by linarith) (by linarith))


theorem fourth_root_young {N z : ℝ} (hN : 0 ≤ N) (hz : 0 ≤ z) :
    N^3*z ≤ N^4+z^4 := by
  rcases le_total z N with h | h
  · have hm := mul_le_mul_of_nonneg_left h (pow_nonneg hN 3)
    nlinarith only [hm,pow_nonneg hz 4]
  · have hp := pow_le_pow_left₀ hN h 3
    have hm := mul_le_mul_of_nonneg_right hp hz
    nlinarith only [hm,pow_nonneg hN 4]

theorem second_budget_sqrt_linear {N T R : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Real.sqrt (bourgainSecondBudget N T R) ≤
      2*N*Real.sqrt R+(Real.sqrt N+T/N)*R := by
  rcases hR.eq_or_lt with he | hRp
  · subst R
    norm_num [bourgainSecondBudget]
  let z := R^(1/4:ℝ)*T^(1/2:ℝ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz4 : z^4 = R*T^2 := by
    dsimp only [z]
    rw [mul_pow,← Real.rpow_mul_natCast hRp.le,← Real.rpow_mul_natCast hT]
    norm_num
  have hRpow : R^(5/4:ℝ) = R*R^(1/4:ℝ) := by
    rw [show (5/4:ℝ) = 1+1/4 by norm_num,Real.rpow_add hRp,Real.rpow_one]
  have hy := mul_le_mul_of_nonneg_right (fourth_root_young hN.le hz) hRp.le
  rw [hz4] at hy
  have ht : R^(5/4:ℝ)*T^(1/2:ℝ)*N ≤ N^2*R+T^2*R^2/N^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
    have he : N^2*(N^2*R+T^2*R^2/N^2) = N^4*R+T^2*R^2 := by
      field_simp
    rw [he,hRpow]
    dsimp only [z] at hy
    nlinarith only [hy]
  let a := Real.sqrt N*R
  let b := N*Real.sqrt R
  let c := (T/N)*R
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha2 : a^2 = N*R^2 := by
    dsimp only [a]; rw [mul_pow,Real.sq_sqrt hN.le]
  have hb2 : b^2 = N^2*R := by
    dsimp only [b]; rw [mul_pow,Real.sq_sqrt hRp.le]
  have hc2 : c^2 = T^2*R^2/N^2 := by
    dsimp only [c]; ring
  have hbudget : bourgainSecondBudget N T R ≤ a^2+2*b^2+c^2 := by
    rw [ha2,hb2,hc2]
    unfold bourgainSecondBudget
    linarith only [ht]
  have hroot : Real.sqrt (bourgainSecondBudget N T R) ≤ a+2*b+c := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hbudget,sq_nonneg b,mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc]
  convert hroot using 1
  dsimp only [a,b,c]
  ring

theorem candidate_five_term_budget {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)))
      (max ((75+4*τ-2*χ-100*σ)/3) ((72+6*τ-2*χ-100*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) := by
  dsimp only
  have hmain := candidate_budget hσ hσ1 hτlo hτhi
  have hχ := le_max_right 0 (τ+1-3*σ)
  have hc := mul_nonneg (by linarith : 0 ≤ 4*σ) (sub_nonneg.mpr hχ)
  have hσp : 0 < 2*σ := by linarith
  have h₁ : (75+4*τ-2*max 0 (τ+1-3*σ)-100*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 13*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 81*σ-64)
    nlinarith only [hc,hp,hq]
  have h₂ : (72+6*τ-2*max 0 (τ+1-3*σ)-100*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 17*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 77*σ-61)
    nlinarith only [hc,hp,hq]
  exact max_le hmain (max_le h₁ h₂)


def familyBandMass {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    (H T V : ℝ) : ℝ :=
  ∑ i ∈ A, ∑ ℓ ∈ bourgainDifferenceSupport (W i),
    (bourgainDifferenceCount (W i) ℓ:ℝ)*bourgainZetaBandMass {ℓ} H T V

theorem family_band_mass_bounds {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ familyBandMass A W H T V ∧
      familyBandMass A W H T V ≤ 4*H*∑ i ∈ A,((W i).card:ℝ)^2 := by
  have hb (ℓ : ℤ) : 0 ≤ bourgainZetaBandMass {ℓ} H T V ∧
      bourgainZetaBandMass {ℓ} H T V ≤ 2*H := by
    simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using
      bourgainZetaBandMass_bounds ({ℓ}:Finset ℤ) hH T V
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hb ℓ).1))
  · have hcomp (i : ι) :
        (∑ ℓ ∈ bourgainDifferenceSupport (W i),
          (bourgainDifferenceCount (W i) ℓ:ℝ)*bourgainZetaBandMass {ℓ} H T V) ≤
            4*H*((W i).card:ℝ)^2 := by
      have hcount : (∑ ℓ ∈ bourgainDifferenceSupport (W i),
          (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤ 2*((W i).card:ℝ)^2 := by
        exact_mod_cast bourgainDifferenceCount_sum_le (W i) (bourgainDifferenceSupport (W i))
      calc
        _ ≤ ∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*(2*H) :=
          Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hb ℓ).2
            (Nat.cast_nonneg _))
        _ = (∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ))*(2*H) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ (2*((W i).card:ℝ)^2)*(2*H) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = _ := by ring
    simpa only [familyBandMass,Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_hi : i ∈ A) => hcomp i)

theorem family_band_partition {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H T : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
      -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T,zetaMomentCriticalNorm t < (2:ℝ)^J) :
    (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
      4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*familyBandMass A W H T ((2:ℝ)^j) := by
  have hlocal (i : ι) (hi : i ∈ A) (ℓ : ℤ)
      (hℓ : ℓ ∈ bourgainDifferenceSupport (W i)) :
      bourgainLocalZetaSquare H ℓ ≤ 2*H+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*
          bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j) := by
    have h := bourgainZetaBand_mass_partition ({ℓ}:Finset ℤ) (a:=1) hH
      (fun m hm => by
        have he := Finset.mem_singleton.mp hm
        simpa only [he] using hrange i hi ℓ hℓ)
      (fun t ht => by simpa only [one_mul] using hterminal t ht)
    simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,
      one_pow,mul_one,one_mul] using h
  have hs := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun ℓ hℓ =>
    mul_le_mul_of_nonneg_left (hlocal i hi ℓ hℓ)
      (Nat.cast_nonneg (bourgainDifferenceCount (W i) ℓ))))
  have he :
      (∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
        (bourgainDifferenceCount (W i) ℓ:ℝ)*(2*H+
          ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*
            bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j))) =
      2*H*(∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
        (bourgainDifferenceCount (W i) ℓ:ℝ))+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*familyBandMass A W H T ((2:ℝ)^j) := by
    simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      ring
    · calc
        _ = ∑ i ∈ A,∑ j ∈ Finset.range J,∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*
              ((2*(2:ℝ)^j)^2*bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = ∑ j ∈ Finset.range J,∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*
              ((2*(2:ℝ)^j)^2*bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j)) := by
          rw [Finset.sum_comm]
        _ = _ := by
          simp only [familyBandMass,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          ring
  rw [he] at hs
  have hcount : (∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
      (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤ 2*∑ i ∈ A,((W i).card:ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast bourgainDifferenceCount_sum_le (W i) (bourgainDifferenceSupport (W i))
  apply hs.trans
  refine add_le_add ?_ le_rfl
  have hm := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 2*H)
  convert hm using 1
  ring

theorem family_band_select :
    ∃ B : ℝ, 0 < B ∧ ∀ {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
      (H T : ℝ), 0 ≤ H →
      (∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
        -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H) →
      ∃ j ∈ Finset.range (bourgainZetaBandCount B T 1),
        (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
          4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
            (bourgainZetaBandCount B T 1:ℝ)*(2*(2:ℝ)^j)^2*
              familyBandMass A W H T ((2:ℝ)^j) := by
  obtain ⟨B,hB,hterminal⟩ := exists_bourgainZetaBand_terminal
  refine ⟨B,hB,?_⟩
  intro ι A W H T hH hrange
  let J := bourgainZetaBandCount B T 1
  let mass := fun j => (2*(2:ℝ)^j)^2*familyBandMass A W H T ((2:ℝ)^j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr (bourgainZetaBandCount_pos B T 1).ne')
  have hp := family_band_partition A W hH hrange
    (fun t ht => by simpa only [one_mul] using hterminal T 1 (by norm_num) t ht)
  refine ⟨j,hj,hp.trans ?_⟩
  have hs : (∑ q ∈ Finset.range J,mass q) ≤ (J:ℝ)*mass j := by
    calc
      _ ≤ ∑ _q ∈ Finset.range J,mass j := Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp
  exact add_le_add le_rfl (by simpa only [mass,mul_assoc] using hs)


theorem absorbed_band_bound {I K Z X A c d μ Y : ℝ}
    (hI : 0 < I) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hμ : 0 ≤ μ)
    (hgram : I ≤ K*Z*X) (hcap : X ≤ A*I)
    (hmixed : X ≤ c*μ+d*Real.sqrt μ) (hmoment : Z^6*μ ≤ Y) :
    I ≤ K*(c*(K*A)^5*Y+d*(K*A)^2*Real.sqrt Y) := by
  have hprod : I ≤ (K*A*Z)*I := by
    have hh := hgram.trans (mul_le_mul_of_nonneg_left hcap (mul_nonneg hK hZ))
    convert hh using 1
    ring
  have hg : 1 ≤ K*A*Z :=
    (mul_le_mul_iff_of_pos_right hI).mp (by simpa only [one_mul] using hprod)
  have hg5 : 1 ≤ (K*A*Z)^5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hg 5
  have hg2 : 1 ≤ (K*A*Z)^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hg 2
  have hfirst : Z*μ ≤ (K*A)^5*Y := by
    calc
      _ ≤ (K*A*Z)^5*(Z*μ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg5 (mul_nonneg hZ hμ)
      _ = (K*A)^5*(Z^6*μ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by positivity)
  have hsqrt : Z^3*Real.sqrt μ ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    simpa only [mul_pow,← pow_mul,Real.sq_sqrt hμ] using hmoment
  have hsecond : Z*Real.sqrt μ ≤ (K*A)^2*Real.sqrt Y := by
    calc
      _ ≤ (K*A*Z)^2*(Z*Real.sqrt μ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg2
          (mul_nonneg hZ (Real.sqrt_nonneg μ))
      _ = (K*A)^2*(Z^3*Real.sqrt μ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg _)
  calc
    I ≤ K*Z*(c*μ+d*Real.sqrt μ) :=
      hgram.trans (mul_le_mul_of_nonneg_left hmixed (mul_nonneg hK hZ))
    _ = K*(c*(Z*μ)+d*(Z*Real.sqrt μ)) := by ring
    _ ≤ K*(c*((K*A)^5*Y)+d*((K*A)^2*Real.sqrt Y)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hfirst hc)
        (mul_le_mul_of_nonneg_left hsecond hd)) hK
    _ = _ := by ring


theorem difference_count_singletons (W : Finset ℝ) (D : Finset ℤ) :
    (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
      (({ℓ} ∩ D).card:ℝ)) = ∑ ℓ ∈ D,(bourgainDifferenceCount W ℓ:ℝ) := by
  calc
    _ = ∑ ℓ ∈ (bourgainDifferenceSupport W).filter (fun ℓ => ℓ ∈ D),
        (bourgainDifferenceCount W ℓ:ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases hm : ℓ ∈ D <;> simp [hm]
    _ = _ := by
      apply Finset.sum_subset
      · intro ℓ hℓ
        exact (Finset.mem_filter.mp hℓ).2
      · intro ℓ hℓ hn
        have hs : ℓ ∉ bourgainDifferenceSupport W := by
          intro hs
          exact hn (Finset.mem_filter.mpr ⟨hs,hℓ⟩)
        rw [bourgainDifferenceCount_eq_zero_of_not_mem W hs,Nat.cast_zero]

theorem family_band_common_shift {ι : Type*}
    (A : Finset ι) (W : ι → Finset ℝ)
    {H T V a b : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmass : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) <
        familyBandMass A W H T V) :
    ∃ u ∈ Ioc (-H) H,(bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card:ℝ)+
        b*Real.sqrt ((bourgainIntegerSlice H T V u).card:ℝ) <
          ∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H T V u,
            (bourgainDifferenceCount (W i) ℓ:ℝ) := by
  let E := A.sigma (fun i => bourgainDifferenceSupport (W i))
  let w := fun x : Σ _i : ι,ℤ => (bourgainDifferenceCount (W x.1) x.2:ℝ)
  let D := fun x : Σ _i : ι,ℤ => ({x.2}:Finset ℤ)
  have hm : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) <
        ∑ x ∈ E,w x*bourgainZetaBandMass (D x) H T V := by
    simpa only [E,w,D,Finset.sum_sigma,familyBandMass] using hmass
  obtain ⟨u,hu,hne,hlower⟩ := bourgain_full_slice_common_shift E w D hH ha hb hm
  refine ⟨u,hu,hne,?_⟩
  simpa only [E,w,D,Finset.sum_sigma,difference_count_singletons] using hlower

theorem physical_family_band_upper {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K N₀ : ℝ, 0 < K ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L), P.N ≤ L → L ≤ P.T →
      ∀ (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A,IsSeparated 2 (W i)) → ∀ V : ℝ,
        let H := P.N^ε
        let U := L+H+1
        let μ := volume.real (bourgainZetaBand U V)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        familyBandMass A W H U V ≤
          (K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2)*
            ((Real.sqrt P.N+P.T/P.N)*(2*Nat.ceil H+1:ℕ)*μ+
              2*P.N*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*μ)) := by
  obtain ⟨M,N₁,hM,hN₁,hlower⟩ := bourgain_subdivided_mixed_difference_counts hε
  obtain ⟨D,E₀,hD,hE₀,hupper⟩ := bourgain_physical_mixed_upper hε
  let K := 2*M*D
  refine ⟨K,max N₁ E₀,by dsimp [K]; positivity,hN₁.trans (le_max_left _ _),?_⟩
  intro P hN σ δ hσ hδ hV L hL hNL hLT A W hsub hsep V
  let H := P.N^ε
  let U := L+H+1
  let μ := volume.real (bourgainZetaBand U V)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let coeff := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let a := coeff*(Real.sqrt P.N+P.T/P.N)
  let b := coeff*(2*P.N)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hcoeff : 0 ≤ coeff := by dsimp [coeff,K,Q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  by_contra hn
  have hmass : a*(2*Nat.ceil H+1:ℕ)*μ+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*μ) < familyBandMass A W H U V := by
    have hh := lt_of_not_ge hn
    change coeff*((Real.sqrt P.N+P.T/P.N)*(2*Nat.ceil H+1:ℕ)*μ+
      2*P.N*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*μ)) < familyBandMass A W H U V at hh
    convert hh using 1
    dsimp only [a,b]
    ring
  obtain ⟨u,hu,_hne,hshift⟩ := family_band_common_shift A W hH ha hb hmass
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let d := ((bourgainIntegerSlice H U V u).card:ℝ)
  let r := 1+2*Real.pi*P.N^ε
  have hsource : S ⊆ P.ordinates := (P.localized_retainedOriginal_union hL A W hsub).1
  have hcard : (S.card:ℝ) ≤ (P.ordinates.card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsource
  have hq : Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ)) ≤ Q := by
    apply Real.sqrt_le_sqrt
    unfold bourgainSecondBudget
    gcongr
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hlinear := second_budget_sqrt_linear hNp P.T_pos.le hd0
  have hl := hlower P ((le_max_left _ _).trans hN) σ δ hσ hδ hV L hL A W hsub hsep
    (bourgainIntegerSlice H U V u)
  have hupp : (∫ v in -r..r,∑ t ∈ S,∑ ℓ ∈ bourgainIntegerSlice H U V u,
      ‖∑ n ∈ P.indices,P.coeff n*dirichletPhase n (t-(ℓ:ℝ)+v)‖^2) ≤
      2*r*D*P.T^ε*(Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ))*
        Real.sqrt (bourgainSecondBudget P.N P.T d)) := by
    have hh := hupper P S hsource L (8*ε) V u r ((le_max_right _ _).trans hN)
      hNL hLT (by linarith : 8*ε ≤ 8)
      (by simpa only [show 8*ε/8 = ε by ring] using (show u ∈ Icc (-H) H from ⟨hu.1.le,hu.2⟩))
      (by dsimp [r]; positivity)
    simpa only [show 8*ε/8 = ε by ring,H,U,d] using hh
  have hprod := mul_le_mul hq hlinear (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ)))
  have hfin : P.V^2*(∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H U V u,
      (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤
      K*P.N^ε*r*P.T^ε*Q*(2*P.N*Real.sqrt d+(Real.sqrt P.N+P.T/P.N)*d) := by
    have hh := hl.trans (mul_le_mul_of_nonneg_left hupp
      (by positivity : 0 ≤ M*P.N^ε))
    have hp := mul_le_mul_of_nonneg_left hprod
      (by dsimp [r]; positivity : 0 ≤ M*P.N^ε*(2*r*D*P.T^ε))
    apply hh.trans
    convert hp using 1 <;> dsimp only [K] <;> ring
  have hstrict := (mul_lt_mul_of_pos_left hshift (sq_pos_of_pos P.V_pos)).trans_le hfin
  have he : P.V^2*(a*d+b*Real.sqrt d) =
      K*P.N^ε*r*P.T^ε*Q*(2*P.N*Real.sqrt d+(Real.sqrt P.N+P.T/P.N)*d) := by
    dsimp only [a,b,coeff,r]
    field_simp [hNp.ne',hVp.ne']
    ring
  change P.V^2*(a*d+b*Real.sqrt d) < _ at hstrict
  rw [he] at hstrict
  exact (lt_irrefl _) hstrict


theorem localized_gram_band {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hgap : 3*ε < 8*σ-6) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ,W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          let H := P.N^ε
          let U := L+H+1
          let J := bourgainZetaBandCount B U 1
          ∃ j ∈ Finset.range J,
            (∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2) ≤
              4*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
              8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*((2:ℝ)^j)^2*
                familyBandMass I W H U ((2:ℝ)^j) := by
  obtain ⟨C₀,δ,hC₀,hδ,hgram⟩ := localized_retained_quadratic (τ:=τ) hσ hε
  obtain ⟨B,hB,hselect⟩ := family_band_select
  let g := 8*σ-6-3*ε
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop (8*C₀^2)))
  let C := max 2 (max C₀ N₁)
  have hCC₀ : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCN₁ : N₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B,C,δ,hB,le_max_left _ _,hδ,?_⟩
  intro P L hL hN hNL hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨W,hW,hrec⟩ := hgram P L hL (hCC₀.trans hN) hNL hTu hV
  refine ⟨W,fun i => ⟨(hW i).1,(hW i).2.1,(hW i).2.2.1⟩,?_⟩
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let S := ∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2
  let R := (P.ordinates.card:ℝ)
  let A := P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)
  let D₀ := (C₀*P.N^(3-4*σ+ε))^2
  have hH : 0 ≤ H := Real.rpow_nonneg hNp.le ε
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD₀ : 0 ≤ D₀ := sq_nonneg _
  have hsmall : 8*H*D₀ ≤ 1 := by
    have he : (8*H*D₀)*P.N^g = 8*C₀^2 := by
      dsimp only [H,D₀]
      rw [mul_pow,← Real.rpow_mul_natCast hNp.le]
      calc
        _ = 8*C₀^2*(P.N^ε*(P.N^((3-4*σ+ε)*2)*P.N^g)) := by ring_nf
        _ = 8*C₀^2*P.N^(ε+(3-4*σ+ε)*2+g) := by
          rw [Real.rpow_add hNp,Real.rpow_add hNp]
          ring
        _ = _ := by
          rw [show ε+(3-4*σ+ε)*2+g = 0 by dsimp only [g]; ring,
            Real.rpow_zero,mul_one]
    apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hNp g)).mp
    rw [he,one_mul]
    exact hN₁ P.N (hCN₁.trans hN)
  obtain ⟨j,hj,hband⟩ := hselect I W H U hH (by
    intro i hi ℓ hℓ
    have hh := bourgainDifferenceSupport_bounds (hW i).2.2.1 hℓ
    dsimp only [U]
    constructor <;> linarith only [hh.1,hh.2])
  have hWcap : (∑ i ∈ I,((W i).card:ℝ)^2) ≤ S := by
    apply Finset.sum_le_sum
    intro i hi
    have hc : ((W i).card:ℝ) ≤ ((P.localized L hL i).ordinates.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card (hW i).1).trans_eq
        (P.localized L hL i).reflectedOrdinates_card
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  let V := (2:ℝ)^j
  let X := familyBandMass I W H U V
  have hX : 0 ≤ X := (family_band_mass_bounds I W hH U V).1
  have hb : (∑ i ∈ I,bourgainZetaDifferenceMoment (W i) H) ≤
      4*H*S+(J:ℝ)*(2*V)^2*X := by
    apply hband.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hWcap (by positivity)) le_rfl
  change S ≤ 2*C₀*A*R+D₀*(∑ i ∈ I,bourgainZetaDifferenceMoment (W i) H) at hrec
  have hcombined := hrec.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hb hD₀))
  have hcoef := mul_le_mul_of_nonneg_right hsmall hS
  have hfinal : S ≤ 4*C₀*A*R+8*D₀*(J:ℝ)*V^2*X := by
    nlinarith only [hcombined,hcoef]
  refine ⟨j,hj,?_⟩
  change S ≤ 4*C*A*R+8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X
  apply hfinal.trans
  dsimp only [D₀,A,R]
  gcongr


theorem physical_twelfth_family_estimate {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ B C K M δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < K ∧ 0 < M ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
        C ≤ P.N → P.N ≤ L → L ≤ P.T →
        L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let H := P.N^ε
        let U := L+H+1
        let J := bourgainZetaBandCount B U 1
        let O := ((2*Nat.ceil H+1:ℕ):ℝ)
        let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
        let G := F*(4*H)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
        let Y := M*U^(2+ε)
        (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
          (8*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
              2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)) := by
  obtain ⟨B,C₀,δ₀,hB,hC₀,hδ₀,hgram⟩ := localized_gram_band (τ:=τ) hσ hε hgap
  obtain ⟨K,N₁,hK,hN₁,hmixed⟩ := physical_family_band_upper hε hε1
  obtain ⟨M,T₀,hM,hT₀,hmoment⟩ := zeta_band_twelfth_bound hε
  let C := max C₀ (max N₁ T₀)
  let δ := min δ₀ 1
  have hCC₀ : C₀ ≤ C := le_max_left _ _
  have hCN₁ : N₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT₀ : T₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  refine ⟨B,C,K,M,δ,hB,hC₀.trans hCC₀,hK,hM,hδ,hδ1,?_⟩
  intro P L hL hN hNL hLT hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hCp : 0 < C := by linarith only [hC₀,hCC₀]
  have hTu₀ : L ≤ P.N^(τ+δ₀) := hTu.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  obtain ⟨W,hW,j,hj,hrec⟩ := hgram P L hL (hCC₀.trans hN) hNL hTu₀ hV₀
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  let S := ∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2
  let small := 8*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)
  let big := F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
    2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)
  let V := (2:ℝ)^j
  let μ := volume.real (bourgainZetaBand U V)
  let X := familyBandMass I W H U V
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hU : 0 < U := by dsimp [U]; positivity
  have hO : 0 ≤ O := Nat.cast_nonneg _
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E,Q]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hbig : 0 ≤ big := by dsimp [big,G]; positivity
  have hsmall : 0 ≤ small := by dsimp [small]; positivity
  have hX : 0 ≤ X := (family_band_mass_bounds I W hH.le U V).1
  have hWcap : (∑ i ∈ I,((W i).card:ℝ)^2) ≤ S := by
    apply Finset.sum_le_sum
    intro i hi
    have hc : ((W i).card:ℝ) ≤ ((P.localized L hL i).ordinates.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card (hW i).1).trans_eq
        (P.localized L hL i).reflectedOrdinates_card
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hcap : X ≤ (4*H)*S := (family_band_mass_bounds I W hH.le U V).2.trans
    (mul_le_mul_of_nonneg_left hWcap (by positivity))
  have hrec' : S ≤ small/2+(F/2)*V^2*X := by
    change S ≤ 4*C₀*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
      8*(C₀*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X at hrec
    have hh : S ≤ 4*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
      8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X := hrec.trans (by gcongr)
    convert hh using 1
    dsimp only [small,F]
    ring
  have hmain : S ≤ small+big := by
    by_cases hs : S ≤ small
    · exact hs.trans (le_add_of_nonneg_right hbig)
    · have hS : 0 < S := hsmall.trans_lt (lt_of_not_ge hs)
      have hgram' : S ≤ F*(V^2)*X := by
        have hh := lt_of_not_ge hs
        nlinarith only [hrec',hh]
      let c := E*(Real.sqrt P.N+P.T/P.N)*O
      let d := E*(2*P.N)*Real.sqrt (2*H*O)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      have hd : 0 ≤ d := by dsimp [d]; positivity
      have hmixed' : X ≤ c*μ+d*Real.sqrt μ := by
        have hm := hmixed P (hCN₁.trans hN) σ δ (by linarith only [hσ]) hδ1 hV
          L hL hNL hLT I W (fun i _ => (hW i).1) (fun i _ => (hW i).2.1) V
        change X ≤ E*((Real.sqrt P.N+P.T/P.N)*O*μ+
          2*P.N*Real.sqrt ((2*H*O)*μ)) at hm
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2*H*O)] at hm
        convert hm using 1
        dsimp only [c,d]
        ring
      have hmoment' : (V^2)^6*μ ≤ Y := by
        have hT : T₀ ≤ U := by
          have ht := (hCT₀.trans hN).trans hNL
          dsimp only [U]
          linarith only [ht,hH]
        simpa only [← pow_mul] using hmoment U V hT (by dsimp [V]; positivity)
      have hh := absorbed_band_bound hS hF (sq_nonneg V) (by positivity : 0 ≤ 4*H)
        hc hd (measureReal_nonneg) hgram' hcap hmixed' hmoment'
      have hbigbound : S ≤ big := by
        convert hh using 1
        dsimp only [big,c,d,G]
        ring
      exact hbigbound.trans (le_add_of_nonneg_left hsmall)
  have hglobal := localized_square_mass P hL
  change (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*(small+big)
  exact hglobal.trans (mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _))


theorem physical_factor_log_bounds (P : LargeValuePattern) {L C K M σ u τ δ ε : ℝ}
    {J : ℕ} (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hJ : 0 < J) (hlogJ : Real.logb P.N (J:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε) :
    let H := P.N^ε
    let U := L+H+1
    let O := ((2*Nat.ceil H+1:ℕ):ℝ)
    let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
    let G := F*(4*H)
    let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
    let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
    let Y := M*U^(2+ε)
    Real.logb P.N F ≤ 6-8*σ+7*ε ∧
      Real.logb P.N G ≤ 6-8*σ+9*ε ∧
      Real.logb P.N E ≤
        heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2-
          2*σ+(τ+10)*ε ∧
      Real.logb P.N Y ≤ 2*u+(τ+7)*ε ∧
      Real.logb P.N O ≤ 2*ε ∧
      Real.logb P.N (Real.sqrt P.N+P.T/P.N) ≤ max (1/2) (τ-1)+2*ε ∧
      Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε := by
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hLp : 0 < L := hNp.trans_le hNL
  have hRp : (0:ℝ) < P.ordinates.card := by exact_mod_cast hR.card_pos
  have hJp : (0:ℝ) < J := by exact_mod_cast hJ
  let H := P.N^ε
  let U := L+H+1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hH1 : 1 ≤ H := Real.one_le_rpow hN.le hε.le
  have hHN : H ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le hε1
  have hU : 0 < U := by dsimp [U]; positivity
  have hO : 0 < O := by dsimp [O]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hbudget := bourgainSecondBudget_pos hNp hTp.le hRp
  have hQ : 0 < Q := Real.sqrt_pos.mpr hbudget
  have hconst (a : ℝ) (ha : 0 < a) (ha100 : a ≤ 100) :
      Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha ha100).trans hlog100
  have hlogH : Real.logb P.N H = ε := Real.logb_rpow hNp hN.ne'
  have hlogT : Real.logb P.N P.T ≤ τ+δ :=
    (Real.logb_le_iff_le_rpow hN hTp).mpr hT
  have hlogL : Real.logb P.N L ≤ u+δ :=
    (Real.logb_le_iff_le_rpow hN hLp).mpr hL
  have hlogV : σ-δ ≤ Real.logb P.N P.V :=
    (Real.le_logb_iff_rpow_le hN hVp).mpr hV
  have hlogO : Real.logb P.N O ≤ 2*ε := by
    have hceil := Nat.ceil_lt_add_one hH.le
    have hOcap : O ≤ 5*H := by
      dsimp only [O]
      push_cast
      linarith only [hceil,hH1]
    have hh := Real.logb_le_logb_of_le hN hO hOcap
    rw [Real.logb_mul (by norm_num : (5:ℝ) ≠ 0) hH.ne',hlogH] at hh
    linarith only [hh,hconst 5 (by norm_num) (by norm_num)]
  have hlogF : Real.logb P.N F ≤ 6-8*σ+7*ε := by
    dsimp only [F]
    rw [Real.logb_mul (by positivity) hJp.ne',
      Real.logb_mul (by norm_num : (16:ℝ) ≠ 0) (by positivity),Real.logb_pow,
      Real.logb_mul hC.ne' (Real.rpow_pos_of_pos hNp _).ne',
      Real.logb_rpow hNp hN.ne']
    norm_num only [Nat.cast_ofNat]
    linarith only [hlogC,hlogJ,hconst 16 (by norm_num) (by norm_num)]
  have hlogG : Real.logb P.N G ≤ 6-8*σ+9*ε := by
    dsimp only [G]
    rw [Real.logb_mul hF.ne' (by positivity),
      Real.logb_mul (by norm_num : (4:ℝ) ≠ 0) hH.ne',hlogH]
    linarith only [hlogF,hconst 4 (by norm_num) (by norm_num)]
  have hlogQ : Real.logb P.N Q ≤
      heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2+ε := by
    have hb := bourgain_budget_log_bound hN hTp.le hRp hT
    have hd := bourgain_doubleZeta_height_slack (τ:=τ)
      (r:=Real.logb P.N (P.ordinates.card:ℝ)) hδ
    dsimp only [Q]
    rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hbudget]
    linarith only [hb,hd,hδε,hε,hconst 3 (by norm_num) (by norm_num)]
  have hlogr : Real.logb P.N (1+2*Real.pi*P.N^ε) ≤ 2*ε := by
    have hp : 0 < 1+2*Real.pi*P.N^ε := by positivity
    have hb : 1+2*Real.pi*P.N^ε ≤ (1+2*Real.pi)*P.N^ε := by
      change 1+2*Real.pi*H ≤ (1+2*Real.pi)*H
      nlinarith only [hH1]
    have hh := Real.logb_le_logb_of_le hN hp hb
    rw [Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hNp ε).ne',
      Real.logb_rpow hNp hN.ne'] at hh
    have hc := hconst (1+2*Real.pi) (by positivity)
      (by linarith only [Real.pi_lt_four])
    linarith only [hh,hc]
  have hlogE : Real.logb P.N E ≤
      heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2-
        2*σ+(τ+10)*ε := by
    dsimp only [E]
    rw [Real.logb_div (by positivity) (by positivity),Real.logb_pow,
      Real.logb_mul (by positivity) hQ.ne',
      Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hTp ε).ne',
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul hK.ne' (Real.rpow_pos_of_pos hNp ε).ne',
      Real.logb_rpow hNp hN.ne',Real.logb_rpow_eq_mul_logb_of_pos hTp]
    norm_num only [Nat.cast_ofNat]
    have ht := mul_le_mul_of_nonneg_left hlogT hε.le
    have he := mul_nonneg hε.le (sub_nonneg.mpr hε1)
    nlinarith only [hlogK,hlogr,hlogQ,hlogV,ht,he,hδε,hε]
  have hlogY : Real.logb P.N Y ≤ 2*u+(τ+7)*ε := by
    have hUcap : U ≤ 3*L := by dsimp only [U]; linarith only [hHN,hNL,hN]
    have hh := Real.logb_le_logb_of_le hN hU hUcap
    rw [Real.logb_mul (by norm_num : (3:ℝ) ≠ 0) hLp.ne'] at hh
    have hlogU : Real.logb P.N U ≤ ε+u+δ := by
      linarith only [hh,hlogL,hconst 3 (by norm_num) (by norm_num)]
    dsimp only [Y]
    rw [Real.logb_mul hM.ne' (Real.rpow_pos_of_pos hU _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hU]
    have hm := mul_le_mul_of_nonneg_left hlogU (by positivity : 0 ≤ 2+ε)
    have hd := mul_le_mul_of_nonneg_left hδε (by positivity : 0 ≤ 2+ε)
    have hu := mul_le_mul_of_nonneg_left huτ hε.le
    have he := mul_nonneg hε.le (sub_nonneg.mpr hε1)
    nlinarith only [hlogM,hm,hd,hu,he]
  have hplus : Real.logb P.N (Real.sqrt P.N+P.T/P.N) ≤ max (1/2) (τ-1)+2*ε := by
    let z := max (1/2:ℝ) (τ-1)+δ
    have hn : Real.sqrt P.N ≤ P.N^z := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_le hN.le
      dsimp only [z]
      linarith only [le_max_left (1/2:ℝ) (τ-1),hδ]
    have ht : P.T/P.N ≤ P.N^z := by
      calc
        _ ≤ P.N^(τ+δ)/P.N := div_le_div_of_nonneg_right hT hNp.le
        _ = P.N^(τ+δ-1) := by rw [Real.rpow_sub hNp,Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by
          dsimp only [z]
          linarith only [le_max_right (1/2:ℝ) (τ-1)])
    have hh := Real.logb_le_logb_of_le hN (by positivity : 0 < Real.sqrt P.N+P.T/P.N)
      (show Real.sqrt P.N+P.T/P.N ≤ 2*P.N^z by linarith only [hn,ht])
    rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (Real.rpow_pos_of_pos hNp z).ne',
      Real.logb_rpow hNp hN.ne'] at hh
    dsimp only [z] at hh
    linarith only [hh,hδε,hconst 2 (by norm_num) (by norm_num)]
  have hsqrt : Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε := by
    rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0 < 2*H*O),
      Real.logb_mul (by positivity) hO.ne',
      Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne',hlogH]
    linarith only [hlogO,hconst 2 (by norm_num) (by norm_num)]
  exact ⟨hlogF,hlogG,hlogE,hlogY,hlogO,hplus,hsqrt⟩


theorem finite_logarithmic_comparison (P : LargeValuePattern)
    {L B C K M σ u τ χ δ ε : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hlogJ : Real.logb P.N
      (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε)
    (hbin : ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ) ≤ 2*P.N^χ)
    (hfinite :
      let I := Finset.range (Nat.floor (P.T/L)+1)
      let H := P.N^ε
      let U := L+H+1
      let J := bourgainZetaBandCount B U 1
      let O := ((2*Nat.ceil H+1:ℕ):ℝ)
      let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
      let G := F*(4*H)
      let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
      let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
      let Y := M*U^(2+ε)
      (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
        (8*C*(P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))*(P.ordinates.card:ℝ)+
          F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
            2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y))) :
    let r := Real.logb P.N (P.ordinates.card:ℝ)
    let g := heathBrownDoubleZetaExponent τ r/2
    2*r ≤ χ+
      max (max (2-2*σ+r) (2*u+4-8*σ+r))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*u) (19-26*σ+g+u))+
      (80+3*τ)*ε := by
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hLp : 0 < L := hNp.trans_le hNL
  have hRp : (0:ℝ) < P.ordinates.card := by exact_mod_cast hR.card_pos
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  let r := Real.logb P.N (P.ordinates.card:ℝ)
  let g := heathBrownDoubleZetaExponent τ r/2
  let profile := max (max (2-2*σ+r) (2*u+4-8*σ+r))
    (max (36-50*σ+g+max (1/2) (τ-1)+2*u) (19-26*σ+g+u))
  let loss := (75+2*τ)*ε
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hU : 0 < U := by dsimp [U]; positivity
  have hJ : 0 < J := bourgainZetaBandCount_pos B U 1
  have hJp : (0:ℝ) < J := by exact_mod_cast hJ
  have hO : 0 < O := by dsimp [O]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hQ : 0 < Q := Real.sqrt_pos.mpr (bourgainSecondBudget_pos hNp hTp.le hRp)
  have hE : 0 < E := by dsimp [E]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hplus : 0 < Real.sqrt P.N+P.T/P.N := by positivity
  have hroot : 0 < Real.sqrt (2*H*O) := by positivity
  obtain ⟨hf,hg,he,hy,ho,hpluslog,hsqrt⟩ :=
    physical_factor_log_bounds P hC hK hM hR hε hε1 hδ hδε huτ hNL hL hT hV
      hJ hlogJ hlogC hlogK hlogM hlog100
  change Real.logb P.N F ≤ 6-8*σ+7*ε at hf
  change Real.logb P.N G ≤ 6-8*σ+9*ε at hg
  change Real.logb P.N E ≤ g-2*σ+(τ+10)*ε at he
  change Real.logb P.N Y ≤ 2*u+(τ+7)*ε at hy
  change Real.logb P.N O ≤ 2*ε at ho
  change Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε at hsqrt
  have hconst (a : ℝ) (ha : 0 < a) (ha100 : a ≤ 100) :
      Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha ha100).trans hlog100
  let a := 8*C*(P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))*(P.ordinates.card:ℝ)
  let b := F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y)
  let c := F*E*(2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hpa : max (2-2*σ+r) (2*u+4-8*σ+r) ≤ profile := le_max_left _ _
  have hpb : 36-50*σ+g+max (1/2) (τ-1)+2*u ≤ profile :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hpc : 19-26*σ+g+u ≤ profile := (le_max_right _ _).trans (le_max_right _ _)
  have hτε := mul_nonneg hτ hε.le
  have halog : Real.logb P.N a ≤ profile+loss := by
    have hp := bourgain_logb_two_power_sum hN
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1)
      (2-2*σ+ε) (2*u+4-8*σ+ε)
    simp only [one_mul,show (1:ℝ)+1 = 2 by norm_num] at hp
    have hm : max (2-2*σ+ε) (2*u+4-8*σ+ε) ≤
        max (2-2*σ+r) (2*u+4-8*σ+r)-r+ε := by
      exact max_le
        (by linarith only [le_max_left (2-2*σ+r) (2*u+4-8*σ+r)])
        (by linarith only [le_max_right (2-2*σ+r) (2*u+4-8*σ+r)])
    dsimp only [a,loss]
    rw [Real.logb_mul (by positivity) hRp.ne',
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num : (8:ℝ) ≠ 0) hC.ne']
    change Real.logb P.N 8+Real.logb P.N C+
      Real.logb P.N (P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))+r ≤ _
    nlinarith only [hp,hm,hpa,hlogC,hconst 8 (by norm_num) (by norm_num),
      hconst 2 (by norm_num) (by norm_num),hε,hτε]
  have hblog : Real.logb P.N b ≤ profile+loss := by
    dsimp only [b,loss]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul hF.ne' hE.ne',
      Real.logb_mul (by positivity) hY.ne',
      Real.logb_mul (x:=(Real.sqrt P.N+P.T/P.N)*O) (y:=G^5) (by positivity) (by positivity),
      Real.logb_mul hplus.ne' hO.ne',Real.logb_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hf,he,hpluslog,ho,hg,hy,hpb,hε]
  have hclog : Real.logb P.N c ≤ profile+loss := by
    dsimp only [c,loss]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul hF.ne' hE.ne',
      Real.logb_mul (x:=2*P.N*Real.sqrt (2*H*O)*G^2) (y:=Real.sqrt Y) (by positivity) (by positivity),
      Real.logb_mul (x:=2*P.N*Real.sqrt (2*H*O)) (y:=G^2) (by positivity) (by positivity),
      Real.logb_mul (by positivity) hroot.ne',
      Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hNp.ne',
      Real.logb_pow,Real.logb_self_eq_one hN,
      Real.sqrt_eq_rpow (x:=Y),Real.logb_rpow_eq_mul_logb_of_pos hY]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hf,he,hsqrt,hg,hy,hpc,hconst 2 (by norm_num) (by norm_num),hε,hτε]
  have habc : a+b+c ≤ 3*P.N^(profile+loss) := by
    have ha' := (Real.logb_le_iff_le_rpow hN ha).mp halog
    have hb' := (Real.logb_le_iff_le_rpow hN hb).mp hblog
    have hc' := (Real.logb_le_iff_le_rpow hN hc).mp hclog
    linarith only [ha',hb',hc']
  have hcore : (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*(a+b+c) := by
    convert hfinite using 1
    dsimp only [a,b,c]
    ring
  have hpower : (P.ordinates.card:ℝ)^2 ≤ 6*P.N^(χ+profile+loss) := by
    calc
      _ ≤ (I.card:ℝ)*(a+b+c) := hcore
      _ ≤ (2*P.N^χ)*(3*P.N^(profile+loss)) :=
        mul_le_mul hbin habc (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hNp,Real.rpow_add hNp,Real.rpow_add hNp]; ring
  have hh := Real.logb_le_logb_of_le hN (sq_pos_of_pos hRp) hpower
  rw [Real.logb_pow,Real.logb_mul (by norm_num : (6:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hNp _).ne',Real.logb_rpow hNp hN.ne'] at hh
  norm_num only [Nat.cast_ofNat] at hh
  change 2*r ≤ χ+profile+(80+3*τ)*ε
  change 2*r ≤ Real.logb P.N 6+(χ+profile+loss) at hh
  dsimp only [loss] at hh
  nlinarith only [hh,hconst 6 (by norm_num) (by norm_num),hε,hτε]


theorem actual_uniform_logarithmic_comparison {σ τ χ ε : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ δ N₀ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 2 ≤ N₀ ∧
      ∀ P : LargeValuePattern, P.ordinates.Nonempty → N₀ ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let r := Real.logb P.N (P.ordinates.card:ℝ)
        let g := heathBrownDoubleZetaExponent τ r/2
        2*r ≤ χ+
          max (max (2-2*σ+r) (2*(τ-χ)+4-8*σ+r))
            (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
              (19-26*σ+g+(τ-χ)))+(80+3*τ)*ε := by
  obtain ⟨B,C,K,M,δ₀,hB,hC,hK,hM,hδ₀,hδ₀1,hfinite⟩ :=
    physical_twelfth_family_estimate (τ:=τ-χ) hσ hε hε1 hgap
  have hτ : 0 ≤ τ := by linarith only [hχ,hmargin]
  obtain ⟨D,Nj,hD,hNj,hbands⟩ :=
    bourgainZetaBandCount_uniform_power (A:=0) (u:=τ+1) hB le_rfl
      (by linarith only [hτ]) hε
  let A := max 100 (max C (max K (max M D)))
  let N₀ := max C (max Nj (Real.exp (|Real.log A|/ε+1)))
  let δ := min δ₀ (min ε ((τ-χ-1)/2))
  have hAp : 0 < A := (by norm_num : (0:ℝ) < 100).trans_le (le_max_left _ _)
  have hCA : C ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hKA : K ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMA : M ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hDA : D ≤ A := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hε (by linarith only [hmargin]))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδmargin : 1+δ ≤ τ-χ := by
    have hh : δ ≤ (τ-χ-1)/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hh,hmargin]
  have hδ1 : δ ≤ 1 := hδδ₀.trans hδ₀1
  refine ⟨δ,N₀,hδ,hδε,hC.trans (le_max_left _ _),?_⟩
  intro P hR hN₀ hTlo hThi hV
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hCN : C ≤ P.N := (le_max_left _ _).trans hN₀
  have hNjN : Nj ≤ P.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN₀
  have hscale : Real.exp (|Real.log A|/ε+1) ≤ P.N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN₀
  have hlogA : Real.logb P.N A ≤ ε :=
    (le_abs_self _).trans (bourgain_abs_logb_le_of_threshold hN hε hscale)
  have hlog (a : ℝ) (ha : 0 < a) (haA : a ≤ A) : Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha haA).trans hlogA
  let L := P.T/P.N^χ
  obtain ⟨hLp,hNL,hLT,_hLlo,hLhi⟩ :=
    bourgain_subdivision_physical_scales hN hχ hδmargin hTlo hThi
  change 0 < L at hLp
  change P.N ≤ L at hNL
  change L ≤ P.T at hLT
  change L ≤ P.N^((τ-χ)+δ) at hLhi
  have hLhi₀ : L ≤ P.N^((τ-χ)+δ₀) := hLhi.trans
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hδδ₀]))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hδδ₀])).trans hV
  have hf := hfinite P L hLp hCN hNL hLT hLhi₀ hV₀
  have hH : 0 < P.N^ε := Real.rpow_pos_of_pos hNp ε
  have hHN : P.N^ε ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le hε1
  have hU : 0 < L+P.N^ε+1 := by positivity
  have hUcap : L+P.N^ε+1 ≤ 3*P.N^(τ+1) := by
    have hLcap : L ≤ P.N^(τ+1) := hLhi.trans
      (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hχ,hδ1]))
    linarith only [hHN,hNL,hN,hLcap]
  have hJcap : (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ D*P.N^ε := by
    simpa only [neg_zero,Real.rpow_zero] using
      hbands P.N (L+P.N^ε+1) hNjN hU.le hUcap
  have hJpos : (0:ℝ) < bourgainZetaBandCount B (L+P.N^ε+1) 1 := by
    exact_mod_cast bourgainZetaBandCount_pos B (L+P.N^ε+1) 1
  have hlogJ : Real.logb P.N (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ 2*ε := by
    have hh := Real.logb_le_logb_of_le hN hJpos hJcap
    rw [Real.logb_mul (by linarith only [hD] : D ≠ 0) hH.ne',
      Real.logb_rpow hNp hN.ne'] at hh
    linarith only [hh,hlog D (by linarith only [hD]) hDA]
  exact finite_logarithmic_comparison P
    (by linarith only [hC]) hK hM hR hε hε1 hτ hδ.le hδε
    (by linarith only [hχ]) hNL hLhi hThi hV hlogJ
    (hlog C (by linarith only [hC]) hCA) (hlog K hK hKA) (hlog M hM hMA)
    (hlog 100 (by norm_num) (le_max_left _ _))
    (bourgain_subdivision_bin_count hN.le P.T_pos hχ) hf


theorem region_zero_loss_comparison {σ τ χ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    let g := heathBrownDoubleZetaExponent τ ρ/2
    2*ρ ≤ χ+
      max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
          (19-26*σ+g+(τ-χ))) := by
  let ε : ℕ → ℝ := fun n => min (poweringAccuracy n) ((8*σ-6)/6)
  have hε (n : ℕ) : 0 < ε n :=
    lt_min (poweringAccuracy_pos n) (by linarith only [hσ])
  have hεa (n : ℕ) : ε n ≤ poweringAccuracy n := min_le_left _ _
  have hε1 (n : ℕ) : ε n ≤ 1 :=
    (hεa n).trans ((poweringAccuracy_le n).trans (by norm_num))
  have hgap (n : ℕ) : 3*ε n < 8*σ-6 := by
    have hh : ε n ≤ (8*σ-6)/6 := min_le_right _ _
    linarith only [hh,hσ]
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds poweringAccuracy_tendsto
      (fun n => (hε n).le) hεa
  have hex (n : ℕ) := actual_uniform_logarithmic_comparison
    hσ hχ hmargin (hε n) (hε1 n) (hgap n)
  choose δ N₀ hδ _hδε _hN₀ hf using hex
  obtain ⟨P,_hNtop,hr,hP⟩ := exists_bourgain_region_family hregion δ N₀ hδ
  let b : ℝ → ℝ := fun r =>
    let g := heathBrownDoubleZetaExponent τ r/2
    χ+max (max (2-2*σ+r) (2*(τ-χ)+4-8*σ+r))
      (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
        (19-26*σ+g+(τ-χ)))
  have hb : Continuous b := by
    dsimp only [b]
    unfold heathBrownDoubleZetaExponent
    fun_prop
  have hright : Filter.Tendsto
      (fun n => b (Real.logb (P n).N ((P n).ordinates.card:ℝ))+(80+3*τ)*ε n)
      Filter.atTop (nhds (b ρ)) := by
    simpa only [mul_zero,add_zero] using
      ((hb.tendsto ρ).comp hr).add (hεlim.const_mul (80+3*τ))
  exact le_of_tendsto_of_tendsto (hr.const_mul 2) hright
    (Filter.Eventually.of_forall (fun n =>
      hf n (P n) (hP n).2.2.2.2.2.1 (hP n).2.1
        (hP n).2.2.1 (hP n).2.2.2.1 (hP n).2.2.2.2.1))

theorem region_cardinality {σ τ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    ρ ≤ 3*(1-σ)*τ/(2*σ) := by
  let χ := max 0 (τ+1-3*σ)
  let g := heathBrownDoubleZetaExponent τ ρ/2
  obtain ⟨hχ,hmargin,_hscale₁,_hscale₂,hclassical⟩ :=
    candidate_scale_budgets hσ hσ1 hτlo hτhi
  have hρ : ρ ≤ max (2-2*σ) (τ+4-6*σ) := by
    simpa only [add_comm (4:ℝ) τ] using hregion.huxley_cardinality
  have hρ1 : ρ ≤ 1 := (hρ.trans hclassical).trans (min_le_left _ _)
  have hρτ : ρ ≤ 4-2*τ := (hρ.trans hclassical).trans (min_le_right _ _)
  have hg : g ≤ 1+ρ/2 := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    unfold heathBrownDoubleZetaExponent
    exact max_le (max_le (by linarith only [hρ1]) (by linarith))
      (by linarith only [hρτ])
  have hd := region_zero_loss_comparison (χ:=χ) hregion
    (by linarith only [hσ]) hχ hmargin
  change 2*ρ ≤ χ+max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
    (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
      (19-26*σ+g+(τ-χ))) at hd
  have hbudget := candidate_five_term_budget hσ hσ1 hτlo hτhi
  change max (max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)))
    (max ((75+4*τ-2*χ-100*σ)/3) ((72+6*τ-2*χ-100*σ)/3)) ≤ _ at hbudget
  rcases max_le_iff.mp hbudget with ⟨habc,hde⟩
  rcases max_le_iff.mp habc with ⟨ha,hbc⟩
  rcases max_le_iff.mp hbc with ⟨hb,hc⟩
  rcases max_le_iff.mp hde with ⟨he,hd'⟩
  have hsplit : 2*ρ-χ ≤ max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
      (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
        (19-26*σ+g+(τ-χ))) := by linarith only [hd]
  rcases le_max_iff.mp hsplit with hs | hl
  · rcases le_max_iff.mp hs with h₁ | h₂
    · linarith only [h₁,ha]
    · linarith only [h₂,hb]
  · rcases le_max_iff.mp hl with h₁ | h₂
    · rcases le_total (1/2:ℝ) (τ-1) with ht | ht
      · rw [max_eq_right ht] at h₁
        linarith only [h₁,hg,hd']
      · rw [max_eq_left ht] at h₁
        linarith only [h₁,hg,he]
    · linarith only [h₂,hg,hc]


theorem bourgain_twelfth_largeValueExponent_range {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτ : τ ∈ Set.Icc (2*(2*σ)/3) (2*σ)) :
    largeValueExponent σ τ ≤ ((((3-3*σ)*τ/(2*σ)):ℝ):EReal) := by
  have hhalf : 1/2 ≤ σ := by linarith only [hσ]
  have hτ0 : 0 ≤ τ := by linarith only [hσ,hτ.1]
  have hcoe := largeValueExponent_coe_toReal hhalf hσ1.le hτ0
  obtain ⟨e,s,hm⟩ := exists_energyRegion_at_largeValueExponent hhalf hσ1.le hτ0
  have hh := region_cardinality
    (show InCardinalityEnergyRegion σ τ (largeValueExponent σ τ).toReal e from ⟨s,hm⟩)
    hσ hσ1 (by linarith only [hτ.1]) hτ.2
  have he : 3*(1-σ)*τ/(2*σ) = (3-3*σ)*τ/(2*σ) := by ring
  rw [he] at hh
  rw [← hcoe]
  exact EReal.coe_le_coe_iff.mpr hh

theorem zeroDensityExponent_le_bourgain_twelfth {σ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) := by
  have hσp : 0 < 2*σ := by linarith only [hσ]
  apply zeroDensityExponent_le_three_div_of_largeValue_bounds
    σ (2*σ) (by linarith only [hσ]) hσ1 hσp
  · intro τ ht
    apply (zetaLargeValueExponent_le_of_bound
      (zetaTwelfth_largeValueBound (by linarith only [hσ]) ht.1)).trans
    apply EReal.coe_le_coe_iff.mpr
    apply (le_div_iff₀ hσp).mpr
    have hc : 0 ≤ 2*(2*σ)-(3-3*σ) := by linarith only [hσ]
    have hh := mul_nonneg hc (show 0 ≤ 4*(2*σ)/3-τ by linarith only [ht.2])
    have hg := mul_nonneg hσp.le
      (show 0 ≤ 3*(4*σ-1)/4-2*σ by linarith only [hσ])
    nlinarith only [hh,hg]
  · exact fun _ ht => bourgain_twelfth_largeValueExponent_range hσ hσ1 ht

/-- The literal Bourgain literature row, obtained by an alternate critical-line
twelfth-moment route, not by assuming the off-critical eighth moment. -/
theorem zeroDensityExponent_le_bourgain_literature {σ : ℝ}
    (hσ : 1867/2347 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_twelfth (by linarith only [hσ]) hσ1

end BourgainTwelfthLiteratureScratch

namespace BourgainTwelfthLiteratureScratchRegression
open BourgainTwelfthLiteratureScratch TaoTrudgianYang2025

example {R a b M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (h : R ≤ a+b*Real.sqrt M) : R^2 ≤ 2*a*R+b^2*M :=
  retained_quadratic hR hM h

example {σ τ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card:ℝ) ≤ C*P.N^ε*((W i).card:ℝ)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          (∑ i ∈ I, ((P.localized L hL i).ordinates.card:ℝ)^2) ≤
            2*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            (C*P.N^(3-4*σ+ε))^2 *
              ∑ i ∈ I, bourgainZetaDifferenceMoment (W i) (P.N^ε) :=
  localized_retained_quadratic hσ hε

example (P : LargeValuePattern) {L : ℝ} (hL : 0 < L) :
    (P.ordinates.card:ℝ)^2 ≤
      ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ)*
        ∑ i ∈ Finset.range (Nat.floor (P.T/L)+1),
          ((P.localized L hL i).ordinates.card:ℝ)^2 :=
  localized_square_mass P hL

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (∫ t in -T..T,zetaMomentCriticalNorm t^12) ≤ C*T^(2+ε) :=
  zeta_twelfth_symmetric hε

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T V : ℝ, T₀ ≤ T → 0 ≤ V →
      V^12*volume.real (bourgainZetaBand T V) ≤ C*T^(2+ε) :=
  zeta_band_twelfth_bound hε

example {σ τ : ℝ} (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) :=
  candidate_budget hσ hσ1 hτlo hτhi

example {σ τ : ℝ} (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    0 ≤ χ ∧ 1 < τ-χ ∧ τ-χ < 24*σ-35/2 ∧ τ-χ < 12*σ-8 ∧
      max (2-2*σ) (τ+4-6*σ) ≤ min 1 (4-2*τ) :=
  candidate_scale_budgets hσ hσ1 hτlo hτhi

example : (31/39:ℝ) < 1867/2347 := by norm_num


example {N z : ℝ} (hN : 0 ≤ N) (hz : 0 ≤ z) : N^3*z ≤ N^4+z^4 :=
  fourth_root_young hN hz

example {N T R : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Real.sqrt (bourgainSecondBudget N T R) ≤
      2*N*Real.sqrt R+(Real.sqrt N+T/N)*R :=
  second_budget_sqrt_linear hN hT hR

example {σ τ : ℝ} (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)))
      (max ((75+4*τ-2*χ-100*σ)/3) ((72+6*τ-2*χ-100*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) :=
  candidate_five_term_budget hσ hσ1 hτlo hτhi

example {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ) (H T V : ℝ) :
    familyBandMass A W H T V =
      ∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
        (bourgainDifferenceCount (W i) ℓ:ℝ)*bourgainZetaBandMass {ℓ} H T V := rfl

example {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ familyBandMass A W H T V ∧
      familyBandMass A W H T V ≤ 4*H*∑ i ∈ A,((W i).card:ℝ)^2 :=
  family_band_mass_bounds A W hH T V

example {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H T : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
      -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T,zetaMomentCriticalNorm t < (2:ℝ)^J) :
    (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
      4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*familyBandMass A W H T ((2:ℝ)^j) :=
  family_band_partition A W hH hrange hterminal

example :
    ∃ B : ℝ, 0 < B ∧ ∀ {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
      (H T : ℝ), 0 ≤ H →
      (∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
        -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H) →
      ∃ j ∈ Finset.range (bourgainZetaBandCount B T 1),
        (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
          4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
            (bourgainZetaBandCount B T 1:ℝ)*(2*(2:ℝ)^j)^2*
              familyBandMass A W H T ((2:ℝ)^j) :=
  family_band_select

example {I K Z X A c d μ Y : ℝ}
    (hI : 0 < I) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hμ : 0 ≤ μ)
    (hgram : I ≤ K*Z*X) (hcap : X ≤ A*I)
    (hmixed : X ≤ c*μ+d*Real.sqrt μ) (hmoment : Z^6*μ ≤ Y) :
    I ≤ K*(c*(K*A)^5*Y+d*(K*A)^2*Real.sqrt Y) :=
  absorbed_band_bound hI hK hZ hA hc hd hμ hgram hcap hmixed hmoment

example (W : Finset ℝ) (D : Finset ℤ) :
    (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
      (({ℓ} ∩ D).card:ℝ)) = ∑ ℓ ∈ D,(bourgainDifferenceCount W ℓ:ℝ) :=
  difference_count_singletons W D

example {ι : Type*}
    (A : Finset ι) (W : ι → Finset ℝ)
    {H T V a b : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmass : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) <
        familyBandMass A W H T V) :
    ∃ u ∈ Ioc (-H) H,(bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card:ℝ)+
        b*Real.sqrt ((bourgainIntegerSlice H T V u).card:ℝ) <
          ∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H T V u,
            (bourgainDifferenceCount (W i) ℓ:ℝ) :=
  family_band_common_shift A W hH ha hb hmass

example {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K N₀ : ℝ, 0 < K ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L), P.N ≤ L → L ≤ P.T →
      ∀ (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A,IsSeparated 2 (W i)) → ∀ V : ℝ,
        let H := P.N^ε
        let U := L+H+1
        let μ := volume.real (bourgainZetaBand U V)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        familyBandMass A W H U V ≤
          (K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2)*
            ((Real.sqrt P.N+P.T/P.N)*(2*Nat.ceil H+1:ℕ)*μ+
              2*P.N*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*μ)) :=
  physical_family_band_upper hε hε1

example {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hgap : 3*ε < 8*σ-6) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ,W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          let H := P.N^ε
          let U := L+H+1
          let J := bourgainZetaBandCount B U 1
          ∃ j ∈ Finset.range J,
            (∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2) ≤
              4*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
              8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*((2:ℝ)^j)^2*
                familyBandMass I W H U ((2:ℝ)^j) :=
  localized_gram_band hσ hε hgap

example {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ B C K M δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < K ∧ 0 < M ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
        C ≤ P.N → P.N ≤ L → L ≤ P.T →
        L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let H := P.N^ε
        let U := L+H+1
        let J := bourgainZetaBandCount B U 1
        let O := ((2*Nat.ceil H+1:ℕ):ℝ)
        let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
        let G := F*(4*H)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
        let Y := M*U^(2+ε)
        (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
          (8*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
              2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)) :=
  physical_twelfth_family_estimate hσ hε hε1 hgap

example (P : LargeValuePattern) {L C K M σ u τ δ ε : ℝ}
    {J : ℕ} (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hJ : 0 < J) (hlogJ : Real.logb P.N (J:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε) :
    let H := P.N^ε
    let U := L+H+1
    let O := ((2*Nat.ceil H+1:ℕ):ℝ)
    let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
    let G := F*(4*H)
    let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
    let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
    let Y := M*U^(2+ε)
    Real.logb P.N F ≤ 6-8*σ+7*ε ∧
      Real.logb P.N G ≤ 6-8*σ+9*ε ∧
      Real.logb P.N E ≤
        heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2-
          2*σ+(τ+10)*ε ∧
      Real.logb P.N Y ≤ 2*u+(τ+7)*ε ∧
      Real.logb P.N O ≤ 2*ε ∧
      Real.logb P.N (Real.sqrt P.N+P.T/P.N) ≤ max (1/2) (τ-1)+2*ε ∧
      Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε :=
  physical_factor_log_bounds P hC hK hM hR hε hε1 hδ hδε huτ hNL hL hT hV hJ hlogJ
    hlogC hlogK hlogM hlog100

example (P : LargeValuePattern)
    {L B C K M σ u τ χ δ ε : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hlogJ : Real.logb P.N
      (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε)
    (hbin : ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ) ≤ 2*P.N^χ)
    (hfinite :
      let I := Finset.range (Nat.floor (P.T/L)+1)
      let H := P.N^ε
      let U := L+H+1
      let J := bourgainZetaBandCount B U 1
      let O := ((2*Nat.ceil H+1:ℕ):ℝ)
      let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
      let G := F*(4*H)
      let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
      let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
      let Y := M*U^(2+ε)
      (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
        (8*C*(P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))*(P.ordinates.card:ℝ)+
          F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
            2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y))) :
    let r := Real.logb P.N (P.ordinates.card:ℝ)
    let g := heathBrownDoubleZetaExponent τ r/2
    2*r ≤ χ+
      max (max (2-2*σ+r) (2*u+4-8*σ+r))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*u) (19-26*σ+g+u))+
      (80+3*τ)*ε :=
  finite_logarithmic_comparison P hC hK hM hR hε hε1 hτ hδ hδε huτ hNL hL hT hV
    hlogJ hlogC hlogK hlogM hlog100 hbin hfinite


example {σ τ χ ε : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ δ N₀ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 2 ≤ N₀ ∧
      ∀ P : LargeValuePattern, P.ordinates.Nonempty → N₀ ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let r := Real.logb P.N (P.ordinates.card:ℝ)
        let g := heathBrownDoubleZetaExponent τ r/2
        2*r ≤ χ+
          max (max (2-2*σ+r) (2*(τ-χ)+4-8*σ+r))
            (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
              (19-26*σ+g+(τ-χ)))+(80+3*τ)*ε :=
  actual_uniform_logarithmic_comparison hσ hχ hmargin hε hε1 hgap


example {σ τ χ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    let g := heathBrownDoubleZetaExponent τ ρ/2
    2*ρ ≤ χ+
      max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
          (19-26*σ+g+(τ-χ))) :=
  region_zero_loss_comparison hregion hσ hχ hmargin

example {σ τ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    ρ ≤ 3*(1-σ)*τ/(2*σ) :=
  region_cardinality hregion hσ hσ1 hτlo hτhi


example {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτ : τ ∈ Set.Icc (2*(2*σ)/3) (2*σ)) :
    largeValueExponent σ τ ≤ ((((3-3*σ)*τ/(2*σ)):ℝ):EReal) :=
  bourgain_twelfth_largeValueExponent_range hσ hσ1 hτ

example {σ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_twelfth hσ hσ1

example {σ : ℝ}
    (hσ : 1867/2347 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_literature hσ hσ1

example : TaoTrudgianYang2025.zeroDensityExponent (1867/2347) ≤
    ((3/(2*(1867/2347)):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_literature le_rfl (by norm_num)

example : TaoTrudgianYang2025.zeroDensityExponent (4/5) ≤
    ((3/(2*(4/5)):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_literature (by norm_num) (by norm_num)

end BourgainTwelfthLiteratureScratchRegression

#print axioms BourgainTwelfthLiteratureScratch.bourgain_twelfth_largeValueExponent_range
#print axioms BourgainTwelfthLiteratureScratch.zeroDensityExponent_le_bourgain_twelfth
#print axioms BourgainTwelfthLiteratureScratch.zeroDensityExponent_le_bourgain_literature

#print axioms BourgainTwelfthLiteratureScratch.region_zero_loss_comparison
#print axioms BourgainTwelfthLiteratureScratch.region_cardinality

#print axioms BourgainTwelfthLiteratureScratch.actual_uniform_logarithmic_comparison

#print axioms BourgainTwelfthLiteratureScratch.retained_quadratic
#print axioms BourgainTwelfthLiteratureScratch.localized_retained_quadratic
#print axioms BourgainTwelfthLiteratureScratch.localized_square_mass
#print axioms BourgainTwelfthLiteratureScratch.zeta_twelfth_symmetric
#print axioms BourgainTwelfthLiteratureScratch.zeta_band_twelfth_bound
#print axioms BourgainTwelfthLiteratureScratch.candidate_budget
#print axioms BourgainTwelfthLiteratureScratch.candidate_scale_budgets
#print axioms BourgainTwelfthLiteratureScratch.fourth_root_young
#print axioms BourgainTwelfthLiteratureScratch.second_budget_sqrt_linear
#print axioms BourgainTwelfthLiteratureScratch.candidate_five_term_budget
#print axioms BourgainTwelfthLiteratureScratch.familyBandMass
#print axioms BourgainTwelfthLiteratureScratch.family_band_mass_bounds
#print axioms BourgainTwelfthLiteratureScratch.family_band_partition
#print axioms BourgainTwelfthLiteratureScratch.family_band_select
#print axioms BourgainTwelfthLiteratureScratch.absorbed_band_bound
#print axioms BourgainTwelfthLiteratureScratch.difference_count_singletons
#print axioms BourgainTwelfthLiteratureScratch.family_band_common_shift
#print axioms BourgainTwelfthLiteratureScratch.physical_family_band_upper
#print axioms BourgainTwelfthLiteratureScratch.localized_gram_band
#print axioms BourgainTwelfthLiteratureScratch.physical_twelfth_family_estimate
#print axioms BourgainTwelfthLiteratureScratch.physical_factor_log_bounds
#print axioms BourgainTwelfthLiteratureScratch.finite_logarithmic_comparison
