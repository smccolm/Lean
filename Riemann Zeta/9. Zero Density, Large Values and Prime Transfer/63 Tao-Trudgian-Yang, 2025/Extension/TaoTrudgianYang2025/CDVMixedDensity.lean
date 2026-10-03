import TaoTrudgianYang2025.IvicSixthGramRow
import TaoTrudgianYang2025.IvicNineteenthDensity
import TaoTrudgianYang2025.BourgainIntegerWindows
import TaoTrudgianYang2025.BourgainDyadicBands
import TaoTrudgianYang2025.BourgainMixedUpper
import TaoTrudgianYang2025.BourgainMixedFamily
import TaoTrudgianYang2025.BourgainPhysicalUpper
import TaoTrudgianYang2025.BourgainComparisonLogarithm
import TaoTrudgianYang2025.BourgainComparisonPowerBudget
import TaoTrudgianYang2025.BourgainDiagonalLoss
import TaoTrudgianYang2025.LargeValueExponentAttainment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The CDV mixed sixth/nineteenth-power density route

Actual large-value patterns feed the smooth Gram entry with all ordered
difference multiplicities retained as weights. A common amplitude band,
a shared integer slice, and the existing two-height Heath--Brown estimate
give the mixed comparison. Smoothing and every selection/coefficient loss
are discharged before passing through actual cardinality-energy realizations.

The slice count is eliminated algebraically; the zero-loss dichotomy then
uses the maximum of the sixth- and nineteenth-power parameter choices.
The exact closed CDV endpoint 279/314 is proved. The existing zeta-side
Ivić bound and two-thirds-range density transfer assemble 24/(30*sigma-11).
Combining with the installed Ivić upper range gives [279/314,17/18].

The source route uses restricted sixth moments, not a full nineteenth moment.
No new source-contract correction, dependency refresh or extra analytic
hypothesis is used here. Frozen counterexamples remain unchanged.
-/

noncomputable section
open Finset MeasureTheory Set
open scoped Interval
namespace TaoTrudgianYang2025
open TaoTrudgianYang2025

private theorem gram_first_moment {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, ∀ H : ℝ, 0 ≤ H →
      ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*C*
        (4*P.N*(P.ordinates.card:ℝ)+Real.sqrt P.N*
          (∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
            ∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
          (P.ordinates.card:ℝ)^2*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
  obtain ⟨C,hC,hbound⟩ := ivicSixthSmoothTrace_localized (2*q)
  refine ⟨C,hC,?_⟩
  intro P H hH
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hQ : 0 < P.scale := by
    have hh : (0:ℝ) < P.scale := by simpa only [P.N_eq_scale] using hN
    exact_mod_cast hh
  have hrow (t : ℝ) (ht : t ∈ P.ordinates) :
      (∑ u ∈ P.ordinates, ‖ivicSixthSmoothTrace P.scale (u-t)‖) ≤
      C*(4*P.N+Real.sqrt P.N*
        (∑ u ∈ P.ordinates, ∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
        (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
    have hpole := bourgain_sum_reciprocal_pow_le_four
      P.ordinates t P.ordinates_oneSeparated hq
    have hpoint (u : ℝ) (hu : u ∈ P.ordinates) :
        ‖ivicSixthSmoothTrace P.scale (u-t)‖ ≤ C*
          (P.N/(1+|u-t|)^(2*q)+Real.sqrt P.N*
            (∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
            Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
      have hh := hbound P.scale hQ (u-t) H hH
      rw [← P.N_eq_scale] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply add_le_add
      · simp only [add_comm (u-t),le_refl]
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (by linarith [P.difference_abs_le_height ht hu]) (Real.sqrt_nonneg _)
    have hsum := Finset.sum_le_sum hpoint
    have he : (∑ u ∈ P.ordinates,C*
          (P.N/(1+|u-t|)^(2*q)+Real.sqrt P.N*
            (∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
            Real.sqrt P.N*(1+P.T)/(1+H)^(2*q))) =
        C*(P.N*(∑ u ∈ P.ordinates,1/(1+|u-t|)^(2*q))+
          Real.sqrt P.N*
            (∑ u ∈ P.ordinates, ∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
          (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
      simp only [div_eq_mul_inv,one_mul,Finset.sum_add_distrib,← Finset.mul_sum,
        Finset.sum_const,nsmul_eq_mul]
      ring
    rw [he] at hsum
    apply hsum.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add (add_le_add (by nlinarith [mul_le_mul_of_nonneg_left hpole hN.le])
      le_rfl) le_rfl
  have hs := Finset.sum_le_sum hrow
  calc
    _ ≤ 2*P.N*(∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖ivicSixthSmoothTrace P.scale (u-t)‖) := P.smooth_sixth_gram
    _ ≤ 2*P.N*(∑ t ∈ P.ordinates,C*(4*P.N+Real.sqrt P.N*
        (∑ u ∈ P.ordinates, ∫ v in -H..H,zetaMomentCriticalNorm (u-t+v))+
        (P.ordinates.card:ℝ)*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      ring

private theorem gram_integer_difference_entry {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, ∀ H : ℝ, 0 ≤ H →
      ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*C*
        (4*P.N*(P.ordinates.card:ℝ)+Real.sqrt P.N*
          (∑ ℓ ∈ bourgainDifferenceSupport P.ordinates,
            (bourgainDifferenceCount P.ordinates ℓ:ℝ)*
              ∫ v in -(H+1)..H+1,zetaMomentCriticalNorm ((ℓ:ℝ)+v))+
          (P.ordinates.card:ℝ)^2*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
  obtain ⟨C,hC,hgram⟩ := gram_first_moment hq
  refine ⟨C,hC,?_⟩
  intro P H hH
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hw := bourgain_difference_window_integral_le P.ordinates
    zetaMomentCriticalNorm continuous_zetaMomentCriticalNorm (fun _ => norm_nonneg _) H hH
  have he :
      (∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ∫ v in -H..H,zetaMomentCriticalNorm (u-t+v)) =
      ∑ p ∈ P.ordinates ×ˢ P.ordinates,
        ∫ v in -H..H,zetaMomentCriticalNorm (p.1-p.2+v) := by
    rw [Finset.sum_product]
    exact Finset.sum_comm
  rw [← he] at hw
  apply (hgram P H hH).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*P.N*C)
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _))) le_rfl

private theorem norm_band_partition {T t : ℝ}
    (ht : t ∈ Icc (-T) T) {J : ℕ}
    (hterminal : zetaMomentCriticalNorm t < (2:ℝ)^J) :
    zetaMomentCriticalNorm t ≤ 1+
      ∑ j ∈ Finset.range J, (2*(2:ℝ)^j)*
        (bourgainZetaBand T ((2:ℝ)^j)).indicator (fun _ => (1:ℝ)) t := by
  have hnonneg (j : ℕ) (_hj : j ∈ Finset.range J) : 0 ≤
      (2*(2:ℝ)^j)*
        (bourgainZetaBand T ((2:ℝ)^j)).indicator (fun _ => (1:ℝ)) t := by
    by_cases h : t ∈ bourgainZetaBand T ((2:ℝ)^j)
    · simp only [Set.indicator_of_mem h,mul_one]
      positivity
    · simp only [Set.indicator_of_notMem h,mul_zero,le_refl]
  by_cases hlow : zetaMomentCriticalNorm t < 1
  · linarith [Finset.sum_nonneg hnonneg]
  · obtain ⟨j,hj,hlo,hhi⟩ := exists_bourgain_dyadic_amplitude
      (le_of_not_gt hlow) (by simpa only [one_mul] using hterminal)
    simp only [one_mul] at hlo hhi
    have hmem : t ∈ bourgainZetaBand T ((2:ℝ)^j) :=
      (mem_bourgainZetaBand _ _ _).mpr ⟨ht.1,ht.2,hlo,hhi⟩
    have hsingle := Finset.single_le_sum hnonneg hj
    rw [Set.indicator_of_mem hmem,mul_one] at hsingle
    linarith

private theorem norm_band_mass_partition (D : Finset ℤ)
    {H T : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ ℓ ∈ D, -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T, zetaMomentCriticalNorm t < (2:ℝ)^J) :
    (∑ ℓ ∈ D, ∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
      2*H*(D.card:ℝ)+
        ∑ j ∈ Finset.range J, (2*(2:ℝ)^j)*
          bourgainZetaBandMass D H T ((2:ℝ)^j) := by
  let g := fun (ℓ : ℤ) (j : ℕ) (u : ℝ) => (2*(2:ℝ)^j)*
    (bourgainZetaBand T ((2:ℝ)^j)).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)
  have hgi (ℓ : ℤ) (j : ℕ) : IntervalIntegrable (g ℓ j) volume (-H) H :=
    (bourgain_indicator_intervalIntegrable
      (measurableSet_bourgainZetaBand T ((2:ℝ)^j)) ℓ (-H) H).const_mul _
  have hgs (ℓ : ℤ) : IntervalIntegrable (fun u => ∑ j ∈ Finset.range J,g ℓ j u)
      volume (-H) H := by
    convert IntervalIntegrable.sum (Finset.range J) (fun j _ => hgi ℓ j) using 1
    ext u
    simp only [Finset.sum_apply]
  have hlocal (ℓ : ℤ) (hℓ : ℓ ∈ D) :
      (∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
        2*H+∑ j ∈ Finset.range J, ∫ u in -H..H,g ℓ j u := by
    have hi : IntervalIntegrable
        (fun u => zetaMomentCriticalNorm ((ℓ:ℝ)+u)) volume (-H) H :=
      (continuous_zetaMomentCriticalNorm.comp
        (continuous_const.add continuous_id)).intervalIntegrable _ _
    calc
      _ ≤ ∫ u in -H..H,1+∑ j ∈ Finset.range J,g ℓ j u := by
        apply intervalIntegral.integral_mono_on (by linarith) hi
          (IntervalIntegrable.add intervalIntegrable_const (hgs ℓ))
        intro u hu
        have ht : (ℓ:ℝ)+u ∈ Icc (-T) T := by
          obtain ⟨hl,hr⟩ := hrange ℓ hℓ
          constructor <;> linarith [hu.1,hu.2]
        exact norm_band_partition ht (hterminal _ ht)
      _ = _ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hgs ℓ),
          intervalIntegral.integral_finsetSum (fun j _ => hgi ℓ j),
          intervalIntegral.integral_const,smul_eq_mul]
        ring
  calc
    _ ≤ ∑ ℓ ∈ D,(2*H+∑ j ∈ Finset.range J, ∫ u in -H..H,g ℓ j u) :=
      Finset.sum_le_sum hlocal
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [mul_comm (D.card:ℝ)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bourgainZetaBandMass_eq_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      exact intervalIntegral.integral_const_mul _ _

private theorem norm_band_select :
    ∃ B : ℝ, 0 < B ∧ ∀ (D : Finset ℤ) (H T : ℝ), 0 ≤ H →
      (∀ ℓ ∈ D, -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H) →
      ∃ j ∈ Finset.range (bourgainZetaBandCount B T 1),
        (∑ ℓ ∈ D, ∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
          2*H*(D.card:ℝ)+(bourgainZetaBandCount B T 1:ℝ)*(2*(2:ℝ)^j)*
            bourgainZetaBandMass D H T ((2:ℝ)^j) := by
  obtain ⟨B,hB,hterminal⟩ := exists_bourgainZetaBand_terminal
  refine ⟨B,hB,?_⟩
  intro D H T hH hrange
  let J := bourgainZetaBandCount B T 1
  let mass := fun j => (2*(2:ℝ)^j)*bourgainZetaBandMass D H T ((2:ℝ)^j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr (bourgainZetaBandCount_pos B T 1).ne')
  have hp := norm_band_mass_partition D hH hrange
    (fun t ht => by simpa only [one_mul] using hterminal T 1 (by norm_num) t ht)
  refine ⟨j,hj,hp.trans ?_⟩
  have hs : (∑ i ∈ Finset.range J,mass i) ≤ (J:ℝ)*mass j := by
    calc
      _ ≤ ∑ _i ∈ Finset.range J,mass j := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  simpa only [mass,mul_assoc] using
    add_le_add (le_refl (2*H*(D.card:ℝ))) hs

private theorem mixed_upper_two_heights {ε : ℝ} (hε : 0 < ε) :
    ∃ C E₀ : ℝ, 0 < C ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (S : Finset ℝ), S ⊆ P.ordinates →
      ∀ H T V u r E F : ℝ, u ∈ Icc (-H) H → 0 ≤ r →
        E₀ ≤ F → F ≤ E → P.T ≤ E → 2*(T+H) ≤ F →
        (∫ v in -r..r, ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
          ‖∑ n ∈ P.indices,P.coeff n*dirichletPhase n (t-(ℓ:ℝ)+v)‖^2) ≤
          2*r*C*E^ε*
            (Real.sqrt (bourgainSecondBudget P.N E (S.card:ℝ))*
              Real.sqrt (bourgainSecondBudget P.N F
                ((bourgainIntegerSlice H T V u).card:ℝ))) := by
  obtain ⟨C,E₀,hC,hE₀,hHB⟩ := bourgain_separated_self_moment hε
  refine ⟨C,E₀,hC,hE₀,?_⟩
  intro P S hsub H T V u r E F hu hr hF hFE hPE hZF
  have hsep : RiemannZeta.GuthMaynard.IsSeparated 1 S := by
    intro t ht w hw htw
    simpa only [Real.dist_eq] using
      P.ordinates_oneSeparated t (hsub ht) w (hsub hw) htw
  have hSloc : ∀ t ∈ S,P.intervalLeft ≤ t ∧ t ≤ P.intervalLeft+E := by
    intro t ht
    have hloc := P.ordinates_in_interval t (hsub ht)
    constructor
    · exact hloc.1
    · linarith [P.interval_length]
  have hZloc : ∀ x ∈ bourgainRealSlice H T V u,
      -(T+H) ≤ x ∧ x ≤ -(T+H)+F := by
    intro x hx
    have hh := bourgainRealSlice_bounds hu x hx
    constructor
    · exact hh.1
    · linarith
  have hS := hHB P S P.intervalLeft E (hF.trans hFE) hsep hSloc
  have hZ := hHB P (bourgainRealSlice H T V u) (-(T+H)) F hF
    (bourgainRealSlice_separated H T V u) hZloc
  rw [bourgainRealSlice_card] at hZ
  have hFp : 0 < F := zero_lt_one.trans_le (hE₀.trans hF)
  have hEp : 0 < E := hFp.trans_le hFE
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hZ' : bourgainSelfMoment P (bourgainRealSlice H T V u) ≤
      C*E^ε*bourgainSecondBudget P.N F ((bourgainIntegerSlice H T V u).card:ℝ) :=
    hZ.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hFp.le hFE hε.le) hC.le)
      (bourgainSecondBudget_nonneg hN.le hFp.le (Nat.cast_nonneg _)))
  have hprod := mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hZ')
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [bourgain_sqrt_common_factor
    (mul_nonneg hC.le (Real.rpow_nonneg hEp.le ε))] at hprod
  have hfin := (bourgain_slice_mixed_integral_cauchySchwarz P S H T V u r hr).trans
    (mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hr))
  convert hfin using 1
  ring

private def differenceBandMass (W : Finset ℝ) (H T V : ℝ) : ℝ :=
  ∑ ℓ ∈ bourgainDifferenceSupport W, (bourgainDifferenceCount W ℓ:ℝ)*
    ∫ u in -H..H,
      (bourgainZetaBand T V).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)

private theorem difference_band_mass_bounds (W : Finset ℝ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ differenceBandMass W H T V ∧
      differenceBandMass W H T V ≤ 4*H*(W.card:ℝ)^2 := by
  have hb (ℓ : ℤ) :
      0 ≤ (∫ u in -H..H,
        (bourgainZetaBand T V).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)) ∧
      (∫ u in -H..H,
        (bourgainZetaBand T V).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)) ≤ 2*H := by
    simpa only [bourgainZetaBandMass_eq_sum,Finset.sum_singleton,
      Finset.card_singleton,Nat.cast_one,mul_one] using
      bourgainZetaBandMass_bounds ({ℓ}:Finset ℤ) hH T V
  constructor
  · exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hb ℓ).1)
  · have hc :
        (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)) ≤
          2*(W.card:ℝ)^2 := by
      exact_mod_cast bourgainDifferenceCount_sum_le W (bourgainDifferenceSupport W)
    calc
      _ ≤ ∑ ℓ ∈ bourgainDifferenceSupport W,
          (bourgainDifferenceCount W ℓ:ℝ)*(2*H) :=
        Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hb ℓ).2
          (Nat.cast_nonneg _))
      _ = (∑ ℓ ∈ bourgainDifferenceSupport W,
          (bourgainDifferenceCount W ℓ:ℝ))*(2*H) := (Finset.sum_mul _ _ _).symm
      _ ≤ (2*(W.card:ℝ)^2)*(2*H) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring

private theorem difference_band_partition (W : Finset ℝ)
    {H T : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ ℓ ∈ bourgainDifferenceSupport W,
      -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T,zetaMomentCriticalNorm t < (2:ℝ)^J) :
    (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
      ∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
      4*H*(W.card:ℝ)^2+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)*differenceBandMass W H T ((2:ℝ)^j) := by
  have hlocal (ℓ : ℤ) (hℓ : ℓ ∈ bourgainDifferenceSupport W) :
      (∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
        2*H+∑ j ∈ Finset.range J,(2*(2:ℝ)^j)*
          (∫ u in -H..H,
            (bourgainZetaBand T ((2:ℝ)^j)).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)) := by
    have hp := norm_band_mass_partition ({ℓ}:Finset ℤ) hH
      (fun m hm => by
        have he : m = ℓ := Finset.mem_singleton.mp hm
        simpa only [he] using hrange ℓ hℓ) hterminal
    simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,
      mul_one,bourgainZetaBandMass_eq_sum] using hp
  have hs := Finset.sum_le_sum (fun ℓ hℓ =>
    mul_le_mul_of_nonneg_left (hlocal ℓ hℓ) (Nat.cast_nonneg (bourgainDifferenceCount W ℓ)))
  have he :
      (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
        (2*H+∑ j ∈ Finset.range J,(2*(2:ℝ)^j)*
          (∫ u in -H..H,
            (bourgainZetaBand T ((2:ℝ)^j)).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)))) =
      2*H*(∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ))+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)*differenceBandMass W H T ((2:ℝ)^j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro ℓ hℓ
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      unfold differenceBandMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      ring
  rw [he] at hs
  apply hs.trans
  refine add_le_add ?_ le_rfl
  have hc : (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)) ≤
      2*(W.card:ℝ)^2 := by
    exact_mod_cast bourgainDifferenceCount_sum_le W (bourgainDifferenceSupport W)
  convert mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*H) using 1
  ring

private theorem difference_band_select :
    ∃ B : ℝ, 0 < B ∧ ∀ (W : Finset ℝ) (H T : ℝ), 0 ≤ H →
      (∀ ℓ ∈ bourgainDifferenceSupport W,-T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H) →
      ∃ j ∈ Finset.range (bourgainZetaBandCount B T 1),
        (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
          ∫ u in -H..H,zetaMomentCriticalNorm ((ℓ:ℝ)+u)) ≤
          4*H*(W.card:ℝ)^2+(bourgainZetaBandCount B T 1:ℝ)*(2*(2:ℝ)^j)*
            differenceBandMass W H T ((2:ℝ)^j) := by
  obtain ⟨B,hB,hterminal⟩ := exists_bourgainZetaBand_terminal
  refine ⟨B,hB,?_⟩
  intro W H T hH hrange
  let J := bourgainZetaBandCount B T 1
  let mass := fun j => (2*(2:ℝ)^j)*differenceBandMass W H T ((2:ℝ)^j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr (bourgainZetaBandCount_pos B T 1).ne')
  have hp := difference_band_partition W hH hrange
    (fun t ht => by simpa only [one_mul] using hterminal T 1 (by norm_num) t ht)
  refine ⟨j,hj,hp.trans ?_⟩
  have hs : (∑ i ∈ Finset.range J,mass i) ≤ (J:ℝ)*mass j := by
    calc
      _ ≤ ∑ _i ∈ Finset.range J,mass j := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  refine add_le_add le_rfl ?_
  simpa only [mass,mul_assoc] using hs

private theorem weighted_mass_self_improvement (k : ℕ)
    {X R μ b A : ℝ} (hX : 0 ≤ X) (hR : 0 < R) (hμ : 0 ≤ μ)
    (hb : 0 ≤ b) (hcap : X ≤ A*R^2)
    (hlower : b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X) :
    b^(k+1)*μ*R ≤ A^k*X := by
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hroot : (μ^(1/((k:ℝ)+1)))^(k+1) = μ := by
    rw [← Real.rpow_mul_natCast hμ]
    norm_num only [Nat.cast_add,Nat.cast_one]
    rw [one_div_mul_cancel hk.ne',Real.rpow_one]
  have hRpow : (R^(2-1/((k:ℝ)+1)))^(k+1) = R^(2*k+1) := by
    rw [← Real.rpow_mul_natCast hR.le]
    have he : (2-1/((k:ℝ)+1))*((k+1:ℕ):ℝ) = ((2*k+1:ℕ):ℝ) := by
      push_cast
      field_simp
      ring
    rw [he,Real.rpow_natCast]
  have hp := pow_le_pow_left₀ (by positivity :
    0 ≤ b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1))) hlower (k+1)
  rw [mul_pow,mul_pow,hroot,hRpow] at hp
  have hcapPow : X^(k+1) ≤ (A*R^2)^k*X := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX hcap k) hX
  apply (mul_le_mul_iff_of_pos_right (pow_pos hR (2*k))).mp
  calc
    _ = b^(k+1)*μ*R^(2*k+1) := by rw [pow_succ R (2*k)]; ring
    _ ≤ (A*R^2)^k*X := hp.trans hcapPow
    _ = _ := by rw [mul_pow,← pow_mul]; ring

private theorem occupancy_rpow_intervalIntegrable (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) {p : ℝ} (hp : 0 ≤ p) (a b : ℝ) :
    IntervalIntegrable (fun u => (bourgainBandOccupancy D S u)^p) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ => (D.card:ℝ)^p) volume a b).mono_fun'
  · exact ((bourgainBandOccupancy_measurable D hS).pow_const p).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    change ‖(bourgainBandOccupancy D S u)^p‖ ≤ (D.card:ℝ)^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (bourgainBandOccupancy_bounds D S u).1 p)]
    exact Real.rpow_le_rpow (bourgainBandOccupancy_bounds D S u).1
      (bourgainBandOccupancy_bounds D S u).2 hp

private theorem slice_integral_rpow_le {H p : ℝ} (hH : 0 < H)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (T V : ℝ) :
    (∫ u in -H..H,((bourgainIntegerSlice H T V u).card:ℝ)^p) ≤
      (2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V))^p := by
  let D := bourgainIntegerCover H T
  let S := bourgainZetaBand T V
  let f := bourgainBandOccupancy D S
  have hS : MeasurableSet S := measurableSet_bourgainZetaBand T V
  have hi := bourgainBandOccupancy_intervalIntegrable D hS (-H) H
  have hpi := occupancy_rpow_intervalIntegrable D hS hp (-H) H
  have horder : -H ≤ H := by linarith
  have hlen : 0 < 2*H := by positivity
  have hμ0 : volume (Ioc (-H) H) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hμtop : volume (Ioc (-H) H) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hj := (Real.concaveOn_rpow hp hp1).le_map_set_average
    (continuous_id.rpow_const (fun _ => Or.inr hp)).continuousOn isClosed_Ici hμ0 hμtop
    (Filter.Eventually.of_forall (fun u => (bourgainBandOccupancy_bounds D S u).1)) hi.1 hpi.1
  have hmeasure : volume.real (Ioc (-H) H) = 2*H := by
    rw [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith)]
    ring
  simp only [setAverage_eq,hmeasure,smul_eq_mul] at hj
  rw [← intervalIntegral.integral_of_le horder,
    ← intervalIntegral.integral_of_le horder] at hj
  simp only [← div_eq_inv_mul] at hj
  have hnonneg : 0 ≤ ∫ u in -H..H,f u :=
    intervalIntegral.integral_nonneg horder
      (fun u _ => (bourgainBandOccupancy_bounds D S u).1)
  have hbound : (∫ u in -H..H,f u^p) ≤
      (2*H)^(1-p)*(∫ u in -H..H,f u)^p := by
    have hm := (div_le_iff₀ hlen).mp hj
    apply hm.trans_eq
    rw [Real.div_rpow hnonneg hlen.le,Real.rpow_sub hlen,Real.rpow_one]
    ring
  simp only [bourgainIntegerSlice_card]
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hnonneg
      (bourgainZetaBandMass_le_measure D hH.le T V) hp) (by positivity)

private theorem full_slice_common_shift_rpow {ι : Type*}
    (A : Finset ι) (w : ι → ℝ) (D : ι → Finset ℤ)
    {H T V a b p : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hmass : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*((2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V))^p) <
      ∑ i ∈ A,w i*bourgainZetaBandMass (D i) H T V) :
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card:ℝ)+
        b*((bourgainIntegerSlice H T V u).card:ℝ)^p <
      ∑ i ∈ A,w i*((D i ∩ bourgainIntegerSlice H T V u).card:ℝ) := by
  let S := bourgainZetaBand T V
  let E := bourgainIntegerCover H T
  let X := bourgainBandOccupancy E S
  let Y := fun u => ∑ i ∈ A,w i*bourgainBandOccupancy (D i) S u
  have hS := measurableSet_bourgainZetaBand T V
  have hXi := bourgainBandOccupancy_intervalIntegrable E hS (-H) H
  have hXp := occupancy_rpow_intervalIntegrable E hS hp.le (-H) H
  have hwi (i : ι) : IntervalIntegrable
      (fun u => w i*bourgainBandOccupancy (D i) S u) volume (-H) H :=
    (bourgainBandOccupancy_intervalIntegrable (D i) hS _ _).const_mul _
  have hYi : IntervalIntegrable Y volume (-H) H := by
    convert IntervalIntegrable.sum A (fun i _ => hwi i) using 1
    ext u
    simp only [Y,Finset.sum_apply]
  let f := fun u => Y u-a*X u-b*(X u)^p
  have hfi : IntervalIntegrable f volume (-H) H :=
    (hYi.sub (hXi.const_mul a)).sub (hXp.const_mul b)
  have hY : (∫ u in -H..H,Y u) =
      ∑ i ∈ A,w i*bourgainZetaBandMass (D i) H T V := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hwi i)]
    simp only [intervalIntegral.integral_const_mul,bourgainZetaBandMass,S]
  have hX : (∫ u in -H..H,X u) ≤
      (2*Nat.ceil H+1:ℕ)*volume.real S :=
    bourgainZetaBandMass_le_measure E hH.le T V
  have hpower : (∫ u in -H..H,(X u)^p) ≤
      (2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real S)^p := by
    simpa only [bourgainIntegerSlice_card] using slice_integral_rpow_le hH hp.le hp1 T V
  have hpos : 0 < ∫ u in -H..H,f u := by
    dsimp only [f]
    rw [intervalIntegral.integral_sub (hYi.sub (hXi.const_mul a)) (hXp.const_mul b),
      intervalIntegral.integral_sub hYi (hXi.const_mul a),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hY]
    have h₁ := mul_le_mul_of_nonneg_left hX ha
    have h₂ := mul_le_mul_of_nonneg_left hpower hb
    change a*(2*Nat.ceil H+1:ℕ)*volume.real S+
      b*((2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real S)^p) < _ at hmass
    nlinarith
  obtain ⟨u,hu,havg⟩ := bourgain_interval_integral_common_shift hH hfi
  have hfpos : 0 < f u := by
    have hh : 0 < 2*H*f u := hpos.trans_le havg
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2*H)).mp hh
  have hucc : u ∈ Icc (-H) H := ⟨hu.1.le,hu.2⟩
  have hfinal : a*((bourgainIntegerSlice H T V u).card:ℝ)+
      b*((bourgainIntegerSlice H T V u).card:ℝ)^p <
      ∑ i ∈ A,w i*((D i ∩ bourgainIntegerSlice H T V u).card:ℝ) := by
    simp_rw [bourgainIntegerSlice_inter_card _ hucc,bourgainIntegerSlice_card]
    change a*X u+b*(X u)^p < Y u
    dsimp only [f] at hfpos
    linarith
  refine ⟨u,hu,?_,hfinal⟩
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hfinal
  simp only [Finset.inter_empty,Finset.card_empty,Nat.cast_zero,mul_zero,
    Real.zero_rpow hp.ne',add_zero,Finset.sum_const_zero] at hfinal
  exact (lt_irrefl 0) hfinal

private theorem gram_actual_weighted_band {q : ℕ} (hq : 0 < q) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ (P : LargeValuePattern) (H : ℝ), 0 ≤ H →
      let U := P.T+H+2
      ∃ j ∈ Finset.range (bourgainZetaBandCount B U 1),
        ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*C*
          (4*P.N*(P.ordinates.card:ℝ)+Real.sqrt P.N*
            (4*(H+1)*(P.ordinates.card:ℝ)^2+
              (bourgainZetaBandCount B U 1:ℝ)*(2*(2:ℝ)^j)*
                differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j))+
            (P.ordinates.card:ℝ)^2*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
  classical
  obtain ⟨C,hC,hgram⟩ := gram_integer_difference_entry hq
  obtain ⟨B,hB,hselect⟩ := difference_band_select
  refine ⟨B,C,hB,hC,?_⟩
  intro P H hH
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hrange : ∀ ℓ ∈ bourgainDifferenceSupport P.ordinates,
      -(P.T+H+2)+(H+1) ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ (P.T+H+2)-(H+1) := by
    intro ℓ hℓ
    obtain ⟨p,hp,hchoice⟩ := Finset.mem_biUnion.mp hℓ
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    have hb := abs_le.mp (P.difference_abs_le_height hp2 hp1)
    have hfloor := Int.floor_le (p.1-p.2)
    have hceil := Int.lt_floor_add_one (p.1-p.2)
    rcases Finset.mem_insert.mp hchoice with rfl | hc
    · constructor <;> linarith [hb.1,hb.2]
    · rw [Finset.mem_singleton] at hc
      rw [hc]
      push_cast
      constructor <;> linarith [hb.1,hb.2]
  obtain ⟨j,hj,hband⟩ := hselect P.ordinates (H+1) (P.T+H+2) (by linarith) hrange
  refine ⟨j,hj,(hgram P H hH).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*P.N*C)
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hband (Real.sqrt_nonneg _))) le_rfl

private theorem band_excess_mass {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    (V/2)^6*volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T, ivicSixthExcess (V/2) t^6 := by
  have hi : IntegrableOn (fun t => ivicSixthExcess (V/2) t^6) (Icc (-T) T) :=
    ((continuous_ivicSixthExcess (V/2)).pow 6).continuousOn.integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => (V/2)^6) (bourgainZetaBand T V) :=
    integrableOn_const (bourgainZetaBand_measure_lt_top T V).ne
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ _ in bourgainZetaBand T V, (V/2)^6 := by simp [mul_comm]
    _ ≤ ∫ t in bourgainZetaBand T V, ivicSixthExcess (V/2) t^6 :=
      setIntegral_mono_on hc (hi.mono_set (bourgainZetaBand_subset_Icc T V))
        (measurableSet_bourgainZetaBand T V) (fun t ht => by
          apply pow_le_pow_left₀ (by positivity : 0 ≤ V/2) _ 6
          have hz := ((mem_bourgainZetaBand T V t).mp ht).2.2.1
          have he : zetaMomentCriticalNorm t-V/2 ≤ ivicSixthExcess (V/2) t :=
            le_max_right _ _
          linarith)
    _ ≤ _ := setIntegral_mono_set hi
      (Filter.Eventually.of_forall (fun _ => by positivity))
      (Filter.Eventually.of_forall (bourgainZetaBand_subset_Icc T V))

private theorem band_two_term_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T V : ℝ, B ≤ T → 0 < V →
      volume.real (bourgainZetaBand T V) ≤ C*T^ε*(T/V^6+T^3/V^19) := by
  let η : ℝ := min ε (1/1000)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hηupper : η ≤ 1/1000 := min_le_right _ _
  obtain ⟨A,D,hA,hD,hmoment⟩ := ivicNineteenth_excess_symmetric_moment hη
  obtain ⟨F,E,hF,hE,hfourth⟩ := bourgainZetaBand_fourth_bound hη
  let K : ℝ := (2:ℝ)^15*(4:ℝ)^(15*(1/8+η))
  have hK : 0 < K := by dsimp [K]; positivity
  let C : ℝ := F*K+(2:ℝ)^19*A
  have hC : 0 < C := by dsimp [C]; positivity
  have hCF : F*K ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hCA : (2:ℝ)^19*A ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_left (by positivity)
  refine ⟨C,max D E,hC,hD.trans (le_max_left _ _),?_⟩
  intro T V hT hV
  have hDT : D ≤ T := (le_max_left _ _).trans hT
  have hET : E ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := hE.trans hET
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hTe : T^η ≤ T^ε := Real.rpow_le_rpow_of_exponent_le hT1 hηε
  by_cases hv : (4*T)^(1/8+η) ≤ V/2
  · have hm := (band_excess_mass hTp.le hV.le).trans (hmoment T (V/2) hDT hv)
    have hb : volume.real (bourgainZetaBand T V) ≤
        ((2:ℝ)^19*A)*T^η*(T/V^6+T^3/V^19) := by
      have hm' : volume.real (bourgainZetaBand T V) ≤
          A*T^η*(T+T^3/(V/2)^13)/(V/2)^6 :=
        (le_div_iff₀ (by positivity : 0 < (V/2)^6)).mpr (by simpa only [mul_comm] using hm)
      apply hm'.trans
      calc
        _ = A*T^η*((2:ℝ)^6*T/V^6+(2:ℝ)^19*T^3/V^19) := by
          field_simp
        _ ≤ _ := by
          have hh : (2:ℝ)^6 ≤ (2:ℝ)^19 := by norm_num
          have hp := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ T/V^6)
          have hTA : 0 ≤ A*T^η := by positivity
          convert mul_le_mul_of_nonneg_left
            (add_le_add_right hp ((2:ℝ)^19*(T^3/V^19))) hTA using 1 <;> ring
    exact hb.trans (mul_le_mul
      (mul_le_mul hCA hTe (by positivity) hC.le) le_rfl (by positivity) (by positivity))
  · have hv' : V ≤ 2*(4*T)^(1/8+η) := by linarith
    have hp : V^15 ≤ K*T^2 := by
      calc
        _ ≤ (2*(4*T)^(1/8+η))^15 := pow_le_pow_left₀ hV.le hv' 15
        _ = K*T^(15*(1/8+η)) := by
          rw [mul_pow,← Real.rpow_mul_natCast (by positivity : 0 ≤ 4*T)]
          norm_num only [Nat.cast_ofNat]
          rw [mul_comm (1/8+η),Real.mul_rpow (by norm_num) hTp.le]
          dsimp [K]
          ring
        _ ≤ K*T^2 := by
          rw [← Real.rpow_two]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hK.le
    have hf := hfourth T V hET hV.le
    have hh := mul_le_mul hp hf (by positivity) (by positivity : 0 ≤ K*T^2)
    have hmass : V^19*volume.real (bourgainZetaBand T V) ≤ (F*K)*T^η*T^3 := by
      rw [Real.rpow_add hTp,Real.rpow_one] at hh
      convert hh using 1 <;> ring
    have hmass' : volume.real (bourgainZetaBand T V) ≤ (F*K)*T^η*T^3/V^19 :=
      (le_div_iff₀ (by positivity : 0 < V^19)).mpr (by simpa only [mul_comm] using hmass)
    calc
      _ ≤ (F*K)*T^η*T^3/V^19  := hmass'
      _ ≤ C*T^ε*T^3/V^19 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hCF hTe (by positivity) hC.le) (by positivity)
      _ ≤ _ := by
        have hh : 0 ≤ C*T^ε*(T/V^6) := by positivity
        convert le_add_of_nonneg_left hh using 1
        ring


private theorem mixed_band_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T V : ℝ, B ≤ T → 0 < V →
      (V ≤ T^(2/13:ℝ) →
        V^19*volume.real (bourgainZetaBand T V) ≤ C*T^(3+ε)) ∧
      (T^(2/13:ℝ) ≤ V →
        V^6*volume.real (bourgainZetaBand T V) ≤ C*T^(1+ε)) := by
  obtain ⟨D,B,hD,hB,hbound⟩ := band_two_term_tail hε
  refine ⟨2*D,B,by positivity,hB,?_⟩
  intro T V hT hV
  have hTp : 0 < T := by linarith
  have hb := hbound T V hT hV
  have he : (T^(2/13:ℝ))^13 = T^2 := by
    rw [← Real.rpow_mul_natCast hTp.le]
    norm_num
  constructor
  · intro hl
    have hp : V^13 ≤ T^2 := by
      simpa only [he] using pow_le_pow_left₀ hV.le hl 13
    calc
      _ ≤ V^19*(D*T^ε*(T/V^6+T^3/V^19)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = D*T^ε*(T*V^13+T^3) := by field_simp
      _ ≤ D*T^ε*(2*T^3) := by
        have hh := mul_le_mul_of_nonneg_left hp hTp.le
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = _ := by rw [Real.rpow_add hTp,Real.rpow_ofNat]; ring
  · intro hl
    have hp : T^2 ≤ V^13 := by
      simpa only [he] using pow_le_pow_left₀ (by positivity : 0 ≤ T^(2/13:ℝ)) hl 13
    have hq : T^3/V^13 ≤ T := by
      apply (div_le_iff₀ (by positivity : 0 < V^13)).mpr
      have hh := mul_le_mul_of_nonneg_left hp hTp.le
      nlinarith
    calc
      _ ≤ V^6*(D*T^ε*(T/V^6+T^3/V^19)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = D*T^ε*(T+T^3/V^13) := by field_simp
      _ ≤ D*T^ε*(2*T) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [Real.rpow_add hTp,Real.rpow_one]; ring

private theorem actual_weighted_band_with_moment {q : ℕ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B C M D : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 40000 ≤ D ∧
      ∀ (P : LargeValuePattern) (H : ℝ), 0 ≤ H → D ≤ P.T+H+2 →
      let U := P.T+H+2
      ∃ j ∈ Finset.range (bourgainZetaBandCount B U 1), ∃ k : ℕ,
        (k = 5 ∨ k = 18) ∧
        0 ≤ differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j) ∧
        differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j) ≤
          4*(H+1)*(P.ordinates.card:ℝ)^2 ∧
        ((2:ℝ)^j)^(k+1)*volume.real (bourgainZetaBand U ((2:ℝ)^j)) ≤
          M*U^((if k = 5 then 1 else 3:ℝ)+ε) ∧
        ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*C*
          (4*P.N*(P.ordinates.card:ℝ)+Real.sqrt P.N*
            (4*(H+1)*(P.ordinates.card:ℝ)^2+
              (bourgainZetaBandCount B U 1:ℝ)*(2*(2:ℝ)^j)*
                differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j))+
            (P.ordinates.card:ℝ)^2*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) := by
  obtain ⟨B,C,hB,hC,hgram⟩ := gram_actual_weighted_band hq
  obtain ⟨M,D,hM,hD,hmoment⟩ := mixed_band_bounds hε
  refine ⟨B,C,M,D,hB,hC,hM,hD,?_⟩
  intro P H hH hDU
  obtain ⟨j,hj,hg⟩ := hgram P H hH
  have hcap := difference_band_mass_bounds P.ordinates
    (by linarith : 0 ≤ H+1) (P.T+H+2) ((2:ℝ)^j)
  have hm := hmoment (P.T+H+2) ((2:ℝ)^j) hDU (by positivity)
  by_cases hl : (2:ℝ)^j ≤ (P.T+H+2)^(2/13:ℝ)
  · exact ⟨j,hj,18,Or.inr rfl,hcap.1,hcap.2,by simpa using hm.1 hl,hg⟩
  · exact ⟨j,hj,5,Or.inl rfl,hcap.1,hcap.2,
      by simpa using hm.2 (lt_of_not_ge hl).le,hg⟩

private theorem weighted_band_dichotomy (k : ℕ)
    {R X V K Y μ b : ℝ} (hR : 0 < R) (hX : 0 ≤ X)
    (hK : 0 < K) (hY : 0 < Y) (hμ : 0 ≤ μ) (hb : 0 ≤ b)
    (hraw : R^2 ≤ K*V*X) (hmoment : V^(k+1)*μ ≤ Y) :
    R ≤ b^(k+1)*K^(k+1)*Y ∨
      b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X := by
  by_cases hc : R ≤ b^(k+1)*K^(k+1)*Y
  · exact Or.inl hc
  right
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hroot : (μ^(1/((k:ℝ)+1)))^(k+1) = μ := by
    rw [← Real.rpow_mul_natCast hμ]
    norm_num only [Nat.cast_add,Nat.cast_one]
    rw [one_div_mul_cancel hk.ne',Real.rpow_one]
  have hRpow : (R^(2-1/((k:ℝ)+1)))^(k+1) = R^(2*k+1) := by
    rw [← Real.rpow_mul_natCast hR.le]
    have he : (2-1/((k:ℝ)+1))*((k+1:ℕ):ℝ) = ((2*k+1:ℕ):ℝ) := by
      push_cast
      field_simp
      ring
    rw [he,Real.rpow_natCast]
  have hh : (b^(k+1)*μ*R^(2*k+1))*(K^(k+1)*Y) ≤
      X^(k+1)*(K^(k+1)*Y) := by
    calc
      _ = (b^(k+1)*K^(k+1)*Y)*(μ*R^(2*k+1)) := by ring
      _ ≤ R*(μ*R^(2*k+1)) :=
        mul_le_mul_of_nonneg_right (lt_of_not_ge hc).le (by positivity)
      _ = μ*(R^2)^(k+1) := by
        simp only [pow_add,pow_mul,pow_one]
        ring
      _ ≤ μ*(K*V*X)^(k+1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg R) hraw (k+1)) hμ
      _ = (K^(k+1)*X^(k+1))*(V^(k+1)*μ) := by
        simp only [mul_pow]
        ring
      _ ≤ (K^(k+1)*X^(k+1))*Y :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = _ := by ring
  apply (pow_le_pow_iff_left₀ (by positivity :
    0 ≤ b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1))) hX (Nat.succ_ne_zero k)).mp
  rw [mul_pow,mul_pow,hroot,hRpow]
  exact (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos hK (k+1)) hY)).mp hh

private theorem actual_component_alternative {q : ℕ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B C M D : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 40000 ≤ D ∧
      ∀ (P : LargeValuePattern) (H d : ℝ), 0 ≤ H → 0 < d → D ≤ P.T+H+2 →
      4*C*P.N*Real.sqrt P.N*(4*(H+1)+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ 32*C*P.N^2 ∨
      let U := P.T+H+2
      let R := (P.ordinates.card:ℝ)
      let J := (bourgainZetaBandCount B U 1:ℝ)
      let K := 16*C*P.N*Real.sqrt P.N*J/P.V^2
      ∃ j ∈ Finset.range (bourgainZetaBandCount B U 1), ∃ k : ℕ,
        (k = 5 ∨ k = 18) ∧
        let μ := volume.real (bourgainZetaBand U ((2:ℝ)^j))
        let X := differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j)
        let b := d^(2/((k:ℝ)+1))/J
        0 < X ∧ (R ≤ b^(k+1)*K^(k+1)*(M*U^((if k = 5 then 1 else 3:ℝ)+ε)) ∨
        (b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X ∧
          b^(k+1)*μ*R ≤ (4*(H+1))^k*X)) := by
  obtain ⟨B,C,M,D,hB,hC,hM,hD,hband⟩ := actual_weighted_band_with_moment hq hε
  refine ⟨B,C,M,D,hB,hC,hM,hD,?_⟩
  intro P H d hH hd hDU hsmall
  let U := P.T+H+2
  let R := (P.ordinates.card:ℝ)
  let J := (bourgainZetaBandCount B U 1:ℝ)
  let K := 16*C*P.N*Real.sqrt P.N*J/P.V^2
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hV := P.V_pos
  have hU : 0 < U := by dsimp [U]; linarith
  have hJ : 0 < J := by
    dsimp only [J]
    exact_mod_cast bourgainZetaBandCount_pos B U 1
  have hK : 0 < K := by dsimp [K]; positivity
  by_cases hdiag : R*P.V^2 ≤ 32*C*P.N^2
  · exact Or.inl hdiag
  right
  have hR : 0 < R := by
    by_contra hh
    have hz : R = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
    rw [hz,zero_mul] at hdiag
    exact hdiag (by positivity)
  obtain ⟨j,hj,k,hk,hX,hcap,hmoment,hgram⟩ := hband P H hH hDU
  let μ := volume.real (bourgainZetaBand U ((2:ℝ)^j))
  let X := differenceBandMass P.ordinates (H+1) U ((2:ℝ)^j)
  let b := d^(2/((k:ℝ)+1))/J
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hμ : 0 ≤ μ := measureReal_nonneg
  have hY : 0 < M*U^((if k = 5 then 1 else 3:ℝ)+ε) := by positivity
  have habs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg R)
  change (R*P.V)^2 ≤ 2*P.N*C*(4*P.N*R+
    Real.sqrt P.N*(4*(H+1)*R^2+J*(2*(2:ℝ)^j)*X)+
    R^2*Real.sqrt P.N*(1+P.T)/(1+H)^(2*q)) at hgram
  have hcore : R^2*P.V^2 ≤
      16*C*P.N^2*R+8*C*P.N*Real.sqrt P.N*J*((2:ℝ)^j)*X := by
    linear_combination 2*hgram+habs
  have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hdiag) hR
  have hweighted : R^2*P.V^2 ≤
      16*C*P.N*Real.sqrt P.N*J*((2:ℝ)^j)*X := by
    nlinarith only [hcore,hstrict]
  have hraw : R^2 ≤ K*((2:ℝ)^j)*X := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hweighted
    convert hh using 1
    dsimp [K]
    ring
  have hXpos : 0 < X := by
    by_contra hn
    have hh : K*(2:ℝ)^j*X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hn)
    exact (not_le_of_gt (sq_pos_of_pos hR)) (hraw.trans hh)
  refine ⟨j,hj,k,hk,hXpos,?_⟩
  rcases weighted_band_dichotomy k hR hX hK hY hμ hb hraw hmoment with hs | hl
  · exact Or.inl hs
  · exact Or.inr ⟨hl,weighted_mass_self_improvement k hX hR hμ hb hcap hl⟩

private theorem difference_count_singletons (W : Finset ℝ) (D : Finset ℤ) :
    (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
      (({ℓ} ∩ D).card:ℝ)) = ∑ ℓ ∈ D,(bourgainDifferenceCount W ℓ:ℝ) := by
  classical
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


private theorem difference_mass_common_shift {ι : Type*}
    (A : Finset ι) (W : ι → Finset ℝ)
    {H T V a b p : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hmass : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*((2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V))^p) <
      ∑ i ∈ A,differenceBandMass (W i) H T V) :
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card:ℝ)+
        b*((bourgainIntegerSlice H T V u).card:ℝ)^p <
      ∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H T V u,(bourgainDifferenceCount (W i) ℓ:ℝ) := by
  classical
  let E := A.sigma (fun i => bourgainDifferenceSupport (W i))
  let w := fun x : Σ _i : ι, ℤ => (bourgainDifferenceCount (W x.1) x.2:ℝ)
  let D := fun x : Σ _i : ι, ℤ => ({x.2}:Finset ℤ)
  have hm : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*((2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V))^p) <
      ∑ x ∈ E,w x*bourgainZetaBandMass (D x) H T V := by
    simpa only [E,w,D,Finset.sum_sigma,bourgainZetaBandMass,bourgainBandOccupancy,
      Finset.sum_singleton,differenceBandMass] using hmass
  obtain ⟨u,hu,hne,hlower⟩ := full_slice_common_shift_rpow E w D hH ha hb hp hp1 hm
  refine ⟨u,hu,hne,?_⟩
  simpa only [E,w,D,Finset.sum_sigma,difference_count_singletons] using hlower

private theorem actual_difference_mass_mixed_comparison
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ M C N₀ E₀ : ℝ, 0 < M ∧ 0 < C ∧ 2 ≤ N₀ ∧ 1 ≤ E₀ ∧
      ∀ P : LargeValuePattern, N₀ ≤ P.N →
      ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A,RiemannZeta.GuthMaynard.IsSeparated 2 (W i)) →
        ∀ H T V a b p E F : ℝ, 0 < H → 0 ≤ a → 0 ≤ b →
          0 < p → p ≤ 1 → E₀ ≤ F → F ≤ E → P.T ≤ E → 2*(T+H) ≤ F →
          a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
            b*((2*H)^(1-p)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V))^p) <
            (∑ i ∈ A,differenceBandMass (W i) H T V) →
          let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
          ∃ u ∈ Ioc (-H) H,
            (bourgainIntegerSlice H T V u).Nonempty ∧
            P.V^2*(a*((bourgainIntegerSlice H T V u).card:ℝ)+
              b*((bourgainIntegerSlice H T V u).card:ℝ)^p) <
            M*P.N^η*(2*(1+2*Real.pi*P.N^η)*C*E^ε*
              (Real.sqrt (bourgainSecondBudget P.N E (S.card:ℝ))*
                Real.sqrt (bourgainSecondBudget P.N F
                  ((bourgainIntegerSlice H T V u).card:ℝ)))) := by
  obtain ⟨M,N₀,hM,hN₀,hlower⟩ := bourgain_subdivided_mixed_difference_counts hη
  obtain ⟨C,E₀,hC,hE₀,hupper⟩ := mixed_upper_two_heights hε
  refine ⟨M,C,N₀,E₀,hM,hC,hN₀,hE₀,?_⟩
  intro P hN σ δ hσ hδ hV L hL A W hsub hsep H T V a b p E F
    hH ha hb hp hp1 hF hFE hPE hZF hmass
  obtain ⟨u,hu,hne,hshift⟩ := difference_mass_common_shift A W hH ha hb hp hp1 hmass
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hsource : S ⊆ P.ordinates :=
    (P.localized_retainedOriginal_union hL A W hsub).1
  have hmixed := hlower P hN σ δ hσ hδ hV L hL A W hsub hsep
    (bourgainIntegerSlice H T V u)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hcompare := hupper P S hsource H T V u (1+2*Real.pi*P.N^η) E F
    ⟨hu.1.le,hu.2⟩ (by positivity) hF hFE hPE hZF
  refine ⟨u,hu,hne,?_⟩
  exact ((mul_lt_mul_of_pos_left hshift (sq_pos_of_pos P.V_pos)).trans_le hmixed).trans_le
    (mul_le_mul_of_nonneg_left hcompare (by positivity))

private theorem difference_band_mass_le_measure (W : Finset ℝ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    differenceBandMass W H T V ≤
      (2*(W.card:ℝ)^2)*((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) := by
  have hm (ℓ : ℤ) :
      (∫ u in -H..H,(bourgainZetaBand T V).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)) ≤
      (2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V) := by
    simpa only [bourgainZetaBandMass,bourgainBandOccupancy,Finset.sum_singleton] using
      bourgainZetaBandMass_le_measure {ℓ} hH T V
  have hcount : (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)) ≤
      2*(W.card:ℝ)^2 := by
    exact_mod_cast bourgainDifferenceCount_sum_le W (bourgainDifferenceSupport W)
  calc
    _ ≤ ∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
        ((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) :=
      Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hm ℓ) (Nat.cast_nonneg _))
    _ = (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ))*
        ((2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)

private theorem difference_band_mass_congr {W Z : Finset ℝ}
    (hc : ∀ ℓ : ℤ,bourgainDifferenceCount W ℓ = bourgainDifferenceCount Z ℓ)
    (H T V : ℝ) :
    differenceBandMass W H T V = differenceBandMass Z H T V := by
  let f := fun ℓ : ℤ => ∫ u in -H..H,
    (bourgainZetaBand T V).indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)+u)
  let D := bourgainDifferenceSupport W ∪ bourgainDifferenceSupport Z
  have hW : (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*f ℓ) =
      ∑ ℓ ∈ D,(bourgainDifferenceCount W ℓ:ℝ)*f ℓ := by
    apply Finset.sum_subset Finset.subset_union_left
    intro ℓ hℓ hn
    rw [bourgainDifferenceCount_eq_zero_of_not_mem W hn,Nat.cast_zero,zero_mul]
  have hZ : (∑ ℓ ∈ bourgainDifferenceSupport Z,(bourgainDifferenceCount Z ℓ:ℝ)*f ℓ) =
      ∑ ℓ ∈ D,(bourgainDifferenceCount Z ℓ:ℝ)*f ℓ := by
    apply Finset.sum_subset Finset.subset_union_right
    intro ℓ hℓ hn
    rw [bourgainDifferenceCount_eq_zero_of_not_mem Z hn,Nat.cast_zero,zero_mul]
  change (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*f ℓ) =
    ∑ ℓ ∈ bourgainDifferenceSupport Z,(bourgainDifferenceCount Z ℓ:ℝ)*f ℓ
  rw [hW,hZ]
  simp_rw [hc]

private theorem band_power_normalization (k : ℕ) {d J : ℝ}
    (hd : 0 ≤ d) (hJ : J ≠ 0) (A : ℝ) :
    (d^(2/((k:ℝ)+1))/J)^(k+1)*(A*J)^(k+1) = d^2*A^(k+1) := by
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hroot : (d^(2/((k:ℝ)+1)))^(k+1) = d^2 := by
    rw [← Real.rpow_mul_natCast hd]
    have he : (2/((k:ℝ)+1))*((k+1:ℕ):ℝ) = (2:ℝ) := by
      push_cast
      exact div_mul_cancel₀ 2 hk.ne'
    rw [he,Real.rpow_two]
  rw [← mul_pow]
  have hi : (d^(2/((k:ℝ)+1))/J)*(A*J) = d^(2/((k:ℝ)+1))*A := by
    field_simp
  rw [hi,mul_pow,hroot]

private theorem actual_retained_component_alternative {q : ℕ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B C M D : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 40000 ≤ D ∧
      ∀ (P : LargeValuePattern) (H d : ℝ), 0 ≤ H → 0 < d → D ≤ P.T+H+2 →
      4*C*P.N*Real.sqrt P.N*(4*(H+1)+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      ∃ W : Finset ℝ, W ⊆ P.reflectedOrdinates ∧
        RiemannZeta.GuthMaynard.IsSeparated 2 W ∧
        (P.ordinates.card:ℝ) ≤ 10*(W.card:ℝ) ∧
        let U := P.T+H+2
        let A := 16*C*P.N*Real.sqrt P.N/P.V^2
        let F := 32*C*P.N^2/P.V^2+
          d^2*M*(U^(1+ε)*A^6+U^(3+ε)*A^19)
        let R := (W.card:ℝ)
        R ≤ F ∨
        ∃ j ∈ Finset.range (bourgainZetaBandCount B U 1), ∃ k : ℕ,
          (k = 5 ∨ k = 18) ∧
          let μ := volume.real (bourgainZetaBand U ((2:ℝ)^j))
          let X := differenceBandMass W (H+1) U ((2:ℝ)^j)
          let b := d^(2/((k:ℝ)+1))/(bourgainZetaBandCount B U 1:ℝ)
          0 < μ ∧ 0 < X ∧
          b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X ∧
          b^(k+1)*μ*R ≤ (4*(H+1))^k*X := by
  obtain ⟨B,C,M,D,hB,hC,hM,hD,hcomp⟩ := actual_component_alternative hq hε
  refine ⟨B,C,M,D,hB,hC,hM,hD,?_⟩
  intro P H d hH hd hDU hsmall
  obtain ⟨W,hW,hsep,hpack⟩ := RiemannZeta.GuthMaynard.exists_dilated_separated_subset
    (by norm_num : (0:ℝ) < 2) P.reflectedOrdinates_isSeparated
  have hpack' : (P.ordinates.card:ℝ) ≤ 10*(W.card:ℝ) := by
    rw [P.reflectedOrdinates_card] at hpack
    norm_num at hpack
    exact_mod_cast hpack
  let S := P.retainedOriginal W
  have hS : S ⊆ P.ordinates := P.retainedOriginal_subset hW
  let Q : LargeValuePattern := {P with
    ordinates := S
    ordinates_in_interval := fun t ht => P.ordinates_in_interval t (hS ht)
    ordinates_oneSeparated := fun t ht u hu htu =>
      P.ordinates_oneSeparated t (hS ht) u (hS hu) htu
    large := fun t ht => P.large t (hS ht)}
  have hmass (T V : ℝ) :
      differenceBandMass S (H+1) T V = differenceBandMass W (H+1) T V :=
    difference_band_mass_congr (P.retainedOriginal_differenceCount W) (H+1) T V
  have hcard : (S.card:ℝ) = (W.card:ℝ) := by
    exact_mod_cast P.retainedOriginal_card W
  have halt := hcomp Q H d hH hd hDU hsmall
  dsimp only [Q] at halt
  simp only [hcard,hmass] at halt
  refine ⟨W,hW,hsep,hpack',?_⟩
  let U := P.T+H+2
  let A := 16*C*P.N*Real.sqrt P.N/P.V^2
  let F := 32*C*P.N^2/P.V^2+d^2*M*(U^(1+ε)*A^6+U^(3+ε)*A^19)
  let R := (W.card:ℝ)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hUp : 0 < U := by dsimp only [U]; linarith [P.T_pos]
  have hV := P.V_pos
  have hAp : 0 < A := by dsimp only [A]; positivity
  have hdiag : 32*C*P.N^2/P.V^2 ≤ F := by
    dsimp only [F]
    exact le_add_of_nonneg_right (by positivity)
  rcases halt with hsmallR | hband
  · left
    exact ((le_div_iff₀ (sq_pos_of_pos hV)).mpr hsmallR).trans hdiag
  obtain ⟨j,hj,k,hk,hXpos,hlarge⟩ := hband
  let J := (bourgainZetaBandCount B U 1:ℝ)
  have hJ : 0 < J := by
    dsimp only [J]
    exact_mod_cast bourgainZetaBandCount_pos B U 1
  rcases hlarge with hsmallR | hlarge
  · left
    change R ≤ F
    have hnorm : (d^(2/((k:ℝ)+1))/J)^(k+1)*
        (16*C*P.N*Real.sqrt P.N*J/P.V^2)^(k+1) = d^2*A^(k+1) := by
      have he : 16*C*P.N*Real.sqrt P.N*J/P.V^2 = A*J := by dsimp only [A]; ring
      rw [he]
      exact band_power_normalization k hd.le hJ.ne' A
    change R ≤ (d^(2/((k:ℝ)+1))/J)^(k+1)*
      (16*C*P.N*Real.sqrt P.N*J/P.V^2)^(k+1)*
        (M*U^((if k = 5 then 1 else 3:ℝ)+ε)) at hsmallR
    rw [hnorm] at hsmallR
    have hnonneg : 0 ≤ 32*C*P.N^2/P.V^2 := by positivity
    rcases hk with rfl | rfl
    · norm_num only [Nat.reduceAdd,ite_true] at hsmallR
      have hx : 0 ≤ d^2*M*(U^(3+ε)*A^19) := by positivity
      dsimp only [F]
      nlinarith only [hsmallR,hnonneg,hx]
    · norm_num only [Nat.reduceAdd,show ¬ (18:ℕ) = 5 by decide,ite_false] at hsmallR
      have hx : 0 ≤ d^2*M*(U^(1+ε)*A^6) := by positivity
      dsimp only [F]
      nlinarith only [hsmallR,hnonneg,hx]
  · right
    refine ⟨j,hj,k,hk,?_,hXpos,hlarge⟩
    by_contra hn
    have hz : volume.real (bourgainZetaBand U ((2:ℝ)^j)) = 0 :=
      le_antisymm (le_of_not_gt hn) measureReal_nonneg
    have hm := difference_band_mass_le_measure W (by linarith : 0 ≤ H+1) U ((2:ℝ)^j)
    rw [hz,mul_zero,mul_zero] at hm
    exact (not_le_of_gt hXpos) hm

private theorem actual_subdivided_common_band {q : ℕ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B C M D : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 40000 ≤ D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (H d : ℝ),
      0 ≤ H → 0 < d → D ≤ L+H+2 →
      4*C*P.N*Real.sqrt P.N*(4*(H+1)+(1+L)/(1+H)^(2*q)) ≤ P.V^2 →
      let U := L+H+2
      let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
      let F := 32*C*P.N^2/P.V^2+
        d^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
      let I := Finset.range (Nat.floor (P.T/L)+1)
      let J := bourgainZetaBandCount B U 1
      (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F ∨
      ∃ (W : ℕ → Finset ℝ) (A : Finset ℕ), A ⊆ I ∧ A.Nonempty ∧
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
          RiemannZeta.GuthMaynard.IsSeparated 2 (W i)) ∧
        (P.ordinates.card:ℝ) ≤ 380*(J:ℝ)*(∑ i ∈ A,((W i).card:ℝ)) ∧
        ∃ j ∈ Finset.range J, ∃ k : ℕ, (k = 5 ∨ k = 18) ∧
          let μ := volume.real (bourgainZetaBand U ((2:ℝ)^j))
          let b := d^(2/((k:ℝ)+1))/(J:ℝ)
          0 < μ ∧
          ∀ i ∈ A,let R := ((W i).card:ℝ)
            let X := differenceBandMass (W i) (H+1) U ((2:ℝ)^j)
            F < R ∧ 0 < X ∧
            b*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X ∧
            b^(k+1)*μ*R ≤ (4*(H+1))^k*X := by
  classical
  obtain ⟨B,C,M,D,hB,hC,hM,hD,hcomp⟩ := actual_retained_component_alternative hq hε
  refine ⟨B,C,M,D,hB,hC,hM,hD,?_⟩
  intro P L hL H d hH hd hDU hsmall
  let U := L+H+2
  let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
  let F := 32*C*P.N^2/P.V^2+d^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let J := bourgainZetaBandCount B U 1
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hVp := P.V_pos
  have hUp : 0 < U := by dsimp only [U]; linarith
  have hF : 0 ≤ F := by dsimp only [F,A₀]; positivity
  have hJ : 0 < J := bourgainZetaBandCount_pos B U 1
  have hlocal (i : ℕ) := hcomp (P.localized L hL i) H d hH hd hDU hsmall
  choose W hsub hsep hpack halt using hlocal
  have hex (i : ℕ) : ∃ j k : ℕ,F < ((W i).card:ℝ) →
      j ∈ Finset.range J ∧ (k = 5 ∨ k = 18) ∧
      let μ := volume.real (bourgainZetaBand U ((2:ℝ)^j))
      let b := d^(2/((k:ℝ)+1))/(J:ℝ)
      let X := differenceBandMass (W i) (H+1) U ((2:ℝ)^j)
      0 < μ ∧ 0 < X ∧
      b*μ^(1/((k:ℝ)+1))*((W i).card:ℝ)^(2-1/((k:ℝ)+1)) ≤ X ∧
      b^(k+1)*μ*((W i).card:ℝ) ≤ (4*(H+1))^k*X := by
    by_cases hi : F < ((W i).card:ℝ)
    · rcases halt i with hs | ⟨j,hj,k,hk,hμ,hX,hfirst,hsecond⟩
      · exact False.elim (not_lt_of_ge hs hi)
      · exact ⟨j,k,fun _ => ⟨hj,hk,hμ,hX,hfirst,hsecond⟩⟩
    · exact ⟨0,0,fun hh => False.elim (hi hh)⟩
  choose j k hband using hex
  let code := fun i => 19*j i+k i
  have hcode : ∀ i ∈ I,F < ((W i).card:ℝ) → code i ∈ Finset.range (19*J) := by
    intro i hi hbig
    have hj := Finset.mem_range.mp (hband i hbig).1
    have hk : k i < 19 := by rcases (hband i hbig).2.1 with hh | hh <;> omega
    apply Finset.mem_range.mpr
    dsimp only [code]
    omega
  obtain ⟨c,hc,hbound⟩ := bourgain_small_large_component_selection I
    (fun i => ((W i).card:ℝ)) (fun i => ((W i).card:ℝ)) code
    hF (by norm_num : (0:ℝ) ≤ 1) (by omega : 0 < 19*J)
    (fun i _ _ => by simp) hcode
  let A := I.filter (fun i => F < ((W i).card:ℝ) ∧ code i = c)
  have hAI : A ⊆ I := Finset.filter_subset _ _
  have hpartition : (P.ordinates.card:ℝ) =
      ∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ) := by
    exact_mod_cast P.card_eq_sum_localized hL
  have hpackTotal : (P.ordinates.card:ℝ) ≤ 10*∑ i ∈ I,((W i).card:ℝ) := by
    rw [hpartition,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpack i)
  have htotal : (P.ordinates.card:ℝ) ≤
      10*(I.card:ℝ)*F+190*(J:ℝ)*(∑ i ∈ A,((W i).card:ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 10)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat,one_mul] at hm
    exact hpackTotal.trans (by convert hm using 1; ring)
  by_cases hs : (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F
  · exact Or.inl hs
  right
  have hA : A.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.sum_empty,mul_zero,add_zero] at htotal
    have hh : 0 ≤ (I.card:ℝ)*F := mul_nonneg (Nat.cast_nonneg _) hF
    exact hs (by nlinarith only [htotal,hh])
  have hglobal : (P.ordinates.card:ℝ) ≤
      380*(J:ℝ)*(∑ i ∈ A,((W i).card:ℝ)) := by
    nlinarith only [htotal,lt_of_not_ge hs]
  let j₀ := c/19
  let k₀ := c%19
  have hj₀ : j₀ ∈ Finset.range J := by
    have hc' := Finset.mem_range.mp hc
    apply Finset.mem_range.mpr
    dsimp only [j₀]
    omega
  have hchosen (i : ℕ) (hi : i ∈ A) : F < ((W i).card:ℝ) ∧ j i = j₀ ∧ k i = k₀ := by
    obtain ⟨_,hbig,hcode⟩ := Finset.mem_filter.mp hi
    have hk : k i < 19 := by rcases (hband i hbig).2.1 with hh | hh <;> omega
    dsimp only [code] at hcode
    refine ⟨hbig,?_,?_⟩ <;> dsimp only [j₀,k₀] <;> omega
  obtain ⟨i₀,hi₀⟩ := hA
  have hb₀ := hband i₀ (hchosen i₀ hi₀).1
  rw [(hchosen i₀ hi₀).2.1,(hchosen i₀ hi₀).2.2] at hb₀
  refine ⟨W,A,hAI,⟨i₀,hi₀⟩,fun i _ => ⟨hsub i,hsep i⟩,hglobal,
    j₀,hj₀,k₀,hb₀.2.1,hb₀.2.2.1,?_⟩
  intro i hi
  have hh := hband i (hchosen i hi).1
  rw [(hchosen i hi).2.1,(hchosen i hi).2.2] at hh
  exact ⟨(hchosen i hi).1,hh.2.2.2⟩

private theorem actual_selected_family_mixed
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ M C N₀ E₀ : ℝ, 0 < M ∧ 0 < C ∧ 2 ≤ N₀ ∧ 1 ≤ E₀ ∧
      ∀ P : LargeValuePattern, N₀ ≤ P.N →
      ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ), A.Nonempty →
      ∀ W : ℕ → Finset ℝ,
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A,RiemannZeta.GuthMaynard.IsSeparated 2 (W i)) →
        ∀ (H T V β E F : ℝ) (k : ℕ), 0 < H → 0 < β →
          E₀ ≤ F → F ≤ E → P.T ≤ E → 2*(T+H) ≤ F →
          (∀ i ∈ A,let R := ((W i).card:ℝ)
            let μ := volume.real (bourgainZetaBand T V)
            let X := differenceBandMass (W i) H T V
            0 < X ∧ β*μ^(1/((k:ℝ)+1))*R^(2-1/((k:ℝ)+1)) ≤ X ∧
              β^(k+1)*μ*R ≤ (4*H)^k*X) →
          let p := 1/((k:ℝ)+1)
          let K := ((2*Nat.ceil H+1:ℕ):ℝ)
          let R := ∑ i ∈ A,((W i).card:ℝ)
          let Z := ∑ i ∈ A,((W i).card:ℝ)^(2-p)
          let a := β^(k+1)*R/(4*(4*H)^k*K)
          let b := β*Z/(4*(2*H)^(1-p)*K^p)
          let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
          ∃ u ∈ Ioc (-H) H,
            (bourgainIntegerSlice H T V u).Nonempty ∧
            P.V^2*(a*((bourgainIntegerSlice H T V u).card:ℝ)+
              b*((bourgainIntegerSlice H T V u).card:ℝ)^p) <
            M*P.N^η*(2*(1+2*Real.pi*P.N^η)*C*E^ε*
              (Real.sqrt (bourgainSecondBudget P.N E (S.card:ℝ))*
                Real.sqrt (bourgainSecondBudget P.N F
                  ((bourgainIntegerSlice H T V u).card:ℝ)))) := by
  obtain ⟨M,C,N₀,E₀,hM,hC,hN₀,hE₀,hcompare⟩ :=
    actual_difference_mass_mixed_comparison hη hε
  refine ⟨M,C,N₀,E₀,hM,hC,hN₀,hE₀,?_⟩
  intro P hN σ δ hσ hδ hV L hL A hA W hsub hsep H T V β E F k
    hH hβ hF hFE hPE hZF hmass
  let p := 1/((k:ℝ)+1)
  let K := ((2*Nat.ceil H+1:ℕ):ℝ)
  let R := ∑ i ∈ A,((W i).card:ℝ)
  let Z := ∑ i ∈ A,((W i).card:ℝ)^(2-p)
  let X := ∑ i ∈ A,differenceBandMass (W i) H T V
  let μ := volume.real (bourgainZetaBand T V)
  let a := β^(k+1)*R/(4*(4*H)^k*K)
  let b := β*Z/(4*(2*H)^(1-p)*K^p)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hK : 0 < K := by dsimp only [K]; positivity
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hX : 0 < X := Finset.sum_pos (fun i hi => (hmass i hi).1) hA
  have hμ : 0 ≤ μ := measureReal_nonneg
  have hfourH : 0 < 4*H := mul_pos (by norm_num) hH
  have htwoH : 0 < 2*H := mul_pos (by norm_num) hH
  have ha : 0 ≤ a := div_nonneg (mul_nonneg (pow_nonneg hβ.le _) hR)
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfourH.le _)) hK.le)
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hβ.le hZ)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg htwoH.le _))
      (Real.rpow_nonneg hK.le _))
  have hfirst : β*μ^p*Z ≤ X := by
    dsimp only [Z,X]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (hmass i hi).2.1)
  have hsecond : β^(k+1)*μ*R ≤ (4*H)^k*X := by
    dsimp only [R,X]
    rw [Finset.mul_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (hmass i hi).2.2)
  have hidentity : a*K*μ+b*((2*H)^(1-p)*(K*μ)^p) =
      (β^(k+1)*μ*R)/(4*(4*H)^k)+(β*μ^p*Z)/4 := by
    rw [Real.mul_rpow hK.le hμ]
    dsimp only [a,b]
    have hlen : (2*H)^(1-p) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    have hkp : K^p ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
    have hhp : (4*H)^k ≠ 0 := (pow_pos (by positivity : 0 < 4*H) k).ne'
    field_simp [hK.ne',hlen,hkp,hhp]
  have hcombined : a*K*μ+b*((2*H)^(1-p)*(K*μ)^p) < X := by
    rw [hidentity]
    have htwo : (β^(k+1)*μ*R)/(4*(4*H)^k) ≤ X/4 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*(4*H)^k)).mpr
      convert hsecond using 1; ring
    have hone : (β*μ^p*Z)/4 ≤ X/4 := div_le_div_of_nonneg_right hfirst (by norm_num)
    linarith only [htwo,hone,hX]
  exact hcompare P hN σ δ hσ hδ hV L hL A W hsub hsep H T V a b p E F
    hH ha hb hp hp1 hF hFE hPE hZF hcombined

private theorem actual_subdivided_physical_comparison
    {q : ℕ} (hq : 0 < q) {ε η θ : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hθ : 0 < θ) :
    ∃ B C M D K N₀ : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 40000 ≤ D ∧
      0 < K ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (_ : 0 < L) (H d σ δ : ℝ),
        N₀ ≤ P.N → P.N ≤ L → L ≤ P.T → 0 ≤ H → H+1 ≤ L →
        0 < d → 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V → D ≤ L+H+2 →
        4*C*P.N*Real.sqrt P.N*(4*(H+1)+(1+L)/(1+H)^(2*q)) ≤ P.V^2 →
        let U := L+H+2
        let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
        let F := 32*C*P.N^2/P.V^2+d^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let J := bourgainZetaBandCount B U 1
        (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F ∨
        ∃ S : Finset ℝ,S ⊆ P.ordinates ∧ S.Nonempty ∧
          (P.ordinates.card:ℝ) ≤ 380*(J:ℝ)*(S.card:ℝ) ∧
          ∃ j ∈ Finset.range J, ∃ k : ℕ,(k = 5 ∨ k = 18) ∧
            let p := 1/((k:ℝ)+1)
            let β := d^(2/((k:ℝ)+1))/(J:ℝ)
            let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
            let a := β^(k+1)*(S.card:ℝ)/(4*(4*(H+1))^k*Q)
            let b := β*((S.card:ℝ)^(2-p)/(I.card:ℝ)^(1-p))/
              (4*(2*(H+1))^(1-p)*Q^p)
            ∃ u ∈ Ioc (-(H+1)) (H+1),
              (bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).Nonempty ∧
              let x := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
              P.V^2*(a*x+b*x^p) <
                K*P.N^η*(1+2*Real.pi*P.N^η)*P.T^θ*
                  (Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ))*
                    Real.sqrt (bourgainSecondBudget P.N L x)) := by
  classical
  obtain ⟨B,C,M,D,hB,hC,hM,hD,hfamily⟩ := actual_subdivided_common_band hq hε
  obtain ⟨M₁,C₁,N₁,E₀,hM₁,hC₁,hN₁,hE₀,hmixed⟩ := actual_selected_family_mixed hη hθ
  let K := 6*M₁*C₁*(8:ℝ)^θ
  let N₀ := max N₁ E₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨B,C,M,D,K,N₀,hB,hC,hM,hD,hK,hN₁.trans (le_max_left _ _),?_⟩
  intro P L hL H d σ δ hN hNL hLT hH hHL hd hσ hδ hV hDU hsmall
  let U := L+H+2
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let J := bourgainZetaBandCount B U 1
  rcases hfamily P L hL H d hH hd hDU hsmall with hs |
    ⟨W,A,hAI,hA,hsource,hpack,j,hj,k,hk,hμ,hbands⟩
  · exact Or.inl hs
  right
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hS := P.localized_retainedOriginal_union hL A W (fun i hi => (hsource i hi).1)
  have hcard : (S.card:ℝ) = ∑ i ∈ A,((W i).card:ℝ) := by exact_mod_cast hS.2.1
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hVp := P.V_pos
  have hUp : 0 < U := by dsimp only [U]; linarith
  have hF : 0 ≤ 32*C*P.N^2/P.V^2+
      d^2*M*(U^(1+ε)*(16*C*P.N*Real.sqrt P.N/P.V^2)^6+
        U^(3+ε)*(16*C*P.N*Real.sqrt P.N/P.V^2)^19) := by positivity
  have hR : 0 < (S.card:ℝ) := by
    rw [hcard]
    exact Finset.sum_pos (fun i hi => hF.trans_lt (hbands i hi).1) hA
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hR)
  let p := 1/((k:ℝ)+1)
  let β := d^(2/((k:ℝ)+1))/(J:ℝ)
  let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
  let Z := ∑ i ∈ A,((W i).card:ℝ)^(2-p)
  have hJ : (0:ℝ) < J := by exact_mod_cast bourgainZetaBandCount_pos B U 1
  have hβ : 0 < β := div_pos (Real.rpow_pos_of_pos hd _) hJ
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hI : 0 < (I.card:ℝ) := by simp only [I,Finset.card_range]; positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hZlower : (S.card:ℝ)^(2-p)/(I.card:ℝ)^(1-p) ≤ Z := by
    have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (f := fun i => ((W i).card:ℝ)) A (by linarith : 1 ≤ 2-p)
      (fun i _ => Nat.cast_nonneg _)
    have he : (2-p)-1 = 1-p := by ring
    rw [he,← hcard] at hh
    have hcards : (A.card:ℝ) ≤ I.card := by exact_mod_cast Finset.card_le_card hAI
    have hj := hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hcards (by linarith : 0 ≤ 1-p)) hZ)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hI _)).mpr (by simpa only [mul_comm] using hj)
  have hN₁ : N₁ ≤ P.N := (le_max_left _ _).trans hN
  have hE : E₀ ≤ 8*L := ((le_max_right _ _).trans hN).trans (by linarith)
  have hHLp : 0 < H+1 := by linarith
  have hcounts := hmixed P hN₁ σ δ hσ hδ hV L hL A hA W
    (fun i hi => (hsource i hi).1) (fun i hi => (hsource i hi).2)
    (H+1) U ((2:ℝ)^j) β (8*P.T) (8*L) k hHLp hβ hE (by linarith)
    (by linarith [P.T_pos]) (by dsimp only [U]; linarith)
    (fun i hi => (hbands i hi).2)
  obtain ⟨u,hu,hne,hcomparison⟩ := hcounts
  let x := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
  let a := β^(k+1)*(S.card:ℝ)/(4*(4*(H+1))^k*Q)
  let b := β*((S.card:ℝ)^(2-p)/(I.card:ℝ)^(1-p))/(4*(2*(H+1))^(1-p)*Q^p)
  have hb : b ≤ β*Z/(4*(2*(H+1))^(1-p)*Q^p) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZlower hβ.le) (by positivity)
  have hleft : P.V^2*(a*x+b*x^p) ≤
      P.V^2*(a*x+(β*Z/(4*(2*(H+1))^(1-p)*Q^p))*x^p) :=
    mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (sq_nonneg P.V)
  change P.V^2*((β^(k+1)*(∑ i ∈ A,((W i).card:ℝ))/(4*(4*(H+1))^k*Q))*x+
    (β*Z/(4*(2*(H+1))^(1-p)*Q^p))*x^p) < _ at hcomparison
  rw [← hcard] at hcomparison
  have hbs := bourgainSecondBudget_eight_height (T := P.T) hNp.le (Nat.cast_nonneg S.card)
  have hbx := bourgainSecondBudget_eight_height (T := L) hNp.le (show 0 ≤ x from Nat.cast_nonneg _)
  have hprod := mul_le_mul (Real.sqrt_le_sqrt hbs) (Real.sqrt_le_sqrt hbx)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [bourgain_sqrt_common_factor (by norm_num : (0:ℝ) ≤ 3)] at hprod
  have hright := mul_le_mul_of_nonneg_left hprod
    (by
      have hTp := P.T_pos
      positivity : 0 ≤ M₁*P.N^η*(2*(1+2*Real.pi*P.N^η)*C₁*(8*P.T)^θ))
  have hfinal := (hleft.trans_lt hcomparison).trans_le (by
    convert hright using 1; ring)
  refine ⟨S,hS.1,hSne,?_,j,hj,k,hk,u,hu,hne,?_⟩
  · simpa only [← hcard] using hpack
  · rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) P.T_pos.le] at hfinal
    convert hfinal using 1
    dsimp only [K]
    ring

private theorem smoothing_absorption_threshold
    {σ τ ν C : ℝ} {q : ℕ}
    (hν : 0 < ν) (hνhalf : ν ≤ 1/2)
    (hgap : (τ+1)*ν < 2*σ-3/2)
    (hq : 1 ≤ (2*q:ℕ)*ν) (hC : 0 < C) :
    ∃ δ N₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 4 ≤ N₀ ∧
      ∀ N L V : ℝ,N₀ ≤ N → N ≤ L → L ≤ N^(τ+δ) → N^(σ-δ) ≤ V →
        0 ≤ L^ν ∧ L^ν+1 ≤ L ∧
        4*C*N*Real.sqrt N*(4*(L^ν+1)+(1+L)/(1+L^ν)^(2*q)) ≤ V^2 := by
  let g := 2*σ-3/2-(τ+1)*ν
  have hg : 0 < g := sub_pos.mpr hgap
  let δ := min 1 (g/8)
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hg (by norm_num))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδg : δ ≤ g/8 := min_le_right _ _
  have hc := (tendsto_rpow_atTop (by positivity : 0 < g/2)).eventually
    (Filter.eventually_ge_atTop (40*C))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp hc
  refine ⟨δ,max 4 N₁,hδ,hδ1,le_max_left _ _,?_⟩
  intro N L V hN hNL hLu hV
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hL4 : 4 ≤ L := hN4.trans hNL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hH1 : 1 ≤ L^ν := Real.one_le_rpow hL1 hν.le
  have hHsqrt : L^ν ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hνhalf
  have hsqrt : Real.sqrt L ≤ L/2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith⟩
  have hHL : L^ν+1 ≤ L := by linarith
  refine ⟨(Real.rpow_pos_of_pos hLp ν).le,hHL,?_⟩
  have htail := ivicSixth_smoothing_tail_le hL1 hq
  have herror : 4*(L^ν+1)+(1+L)/(1+L^ν)^(2*q) ≤ 10*L^ν := by
    linarith only [htail,hH1]
  have hcoef : 40*C ≤ N^(g/2) := hN₁ N ((le_max_right _ _).trans hN)
  have hheight : L^ν ≤ N^((τ+δ)*ν) := by
    have hh := Real.rpow_le_rpow hLp.le hLu hν.le
    rwa [← Real.rpow_mul hNp.le] at hh
  have hNs : N*Real.sqrt N = N^(3/2:ℝ) := by
    calc
      _ = N^(1:ℝ)*N^(1/2:ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hexp : g/2+3/2+(τ+δ)*ν ≤ 2*(σ-δ) := by
    have hm : (τ+δ)*ν ≤ (τ+1)*ν :=
      mul_le_mul_of_nonneg_right (by linarith) hν.le
    dsimp only [g] at hδg ⊢
    nlinarith only [hδg,hm,hgap]
  have hVpow : N^(2*(σ-δ)) ≤ V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    simpa only [Nat.cast_ofNat,mul_comm] using hh
  calc
    _ ≤ 4*C*N*Real.sqrt N*(10*L^ν) :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ = (40*C)*(N*Real.sqrt N)*L^ν := by ring
    _ ≤ N^(g/2)*(N*Real.sqrt N)*N^((τ+δ)*ν) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hheight
        (Real.rpow_nonneg hLp.le _) (by positivity)
    _ = N^(g/2+3/2+(τ+δ)*ν) := by
      rw [hNs,← Real.rpow_add hNp,← Real.rpow_add hNp]
    _ ≤ N^(2*(σ-δ)) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ ≤ _ := hVpow

private theorem actual_power_window_comparison
    {σ τ ν ε η θ ζ : ℝ} (hσ : 3/4 < σ)
    (hν : 0 < ν) (hνhalf : ν ≤ 1/2) (hgap : (τ+1)*ν < 2*σ-3/2)
    (hε : 0 < ε) (hη : 0 < η) (hθ : 0 < θ) (hζ : 0 < ζ) :
    ∃ B C M K δ N₀ : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 0 < K ∧
      0 < δ ∧ δ ≤ 1 ∧ δ ≤ ζ ∧ 4 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L d : ℝ),
        N₀ ≤ P.N → P.N ≤ L → L ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(σ-δ) ≤ P.V → 0 < d →
        let H := L^ν
        let U := L+H+2
        let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
        let F := 32*C*P.N^2/P.V^2+d^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let J := bourgainZetaBandCount B U 1
        (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F ∨
        ∃ S : Finset ℝ,S ⊆ P.ordinates ∧ S.Nonempty ∧
          (P.ordinates.card:ℝ) ≤ 380*(J:ℝ)*(S.card:ℝ) ∧
          ∃ j ∈ Finset.range J, ∃ k : ℕ,(k = 5 ∨ k = 18) ∧
            let p := 1/((k:ℝ)+1)
            let β := d^(2/((k:ℝ)+1))/(J:ℝ)
            let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
            let a := β^(k+1)*(S.card:ℝ)/(4*(4*(H+1))^k*Q)
            let b := β*((S.card:ℝ)^(2-p)/(I.card:ℝ)^(1-p))/
              (4*(2*(H+1))^(1-p)*Q^p)
            ∃ u ∈ Ioc (-(H+1)) (H+1),
              (bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).Nonempty ∧
              let x := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
              P.V^2*(a*x+b*x^p) <
                K*P.N^η*(1+2*Real.pi*P.N^η)*P.T^θ*
                  (Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ))*
                    Real.sqrt (bourgainSecondBudget P.N L x)) := by
  obtain ⟨q,hq⟩ := exists_nat_gt (1/ν)
  have hq0 : 0 < q := by
    have hh : (0:ℝ) < q := (div_pos (by norm_num) hν).trans hq
    exact_mod_cast hh
  have hqν : 1 ≤ (2*q:ℕ)*ν := by
    have hh := (div_lt_iff₀ hν).mp hq
    push_cast
    nlinarith
  obtain ⟨B,C,M,D,K,N₁,hB,hC,hM,hD,hK,hN₁,hphysical⟩ :=
    actual_subdivided_physical_comparison hq0 hε hη hθ
  obtain ⟨δ₀,N₂,hδ₀,hδ₀1,hN₂,hsmoothing⟩ :=
    smoothing_absorption_threshold hν hνhalf hgap hqν hC
  let δ := min δ₀ ζ
  let N₀ := max 4 (max N₁ (max N₂ D))
  have hδ : 0 < δ := lt_min hδ₀ hζ
  have hδold : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδold.trans hδ₀1
  refine ⟨B,C,M,K,δ,N₀,hB,hC,hM,hK,hδ,hδ1,min_le_right _ _,le_max_left _ _,?_⟩
  intro P L d hN hNL hLT hTu hV hd
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hL : 0 < L := hNp.trans_le hNL
  have hNN₁ : N₁ ≤ P.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNN₂ : N₂ ≤ P.N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hND : D ≤ P.N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hLu₀ : L ≤ P.N^(τ+δ₀) := (hLT.trans hTu).trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  obtain ⟨hH,hHL,hsmall⟩ := hsmoothing P.N L P.V hNN₂ hNL hLu₀ hV₀
  exact hphysical P L hL (L^ν) d σ δ hNN₁ hNL hLT hH hHL hd
    (by linarith) hδ1 hV (by linarith) hsmall

private theorem half_le_max_weighted {a d p : ℝ} (hp : p ≤ 1/2) :
    (a+d)/2 ≤ max a (p*a+(1-p)*d) := by
  rcases le_total a d with had | hda
  · have hh := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr had)
    exact (by nlinarith only [hh] : (a+d)/2 ≤ p*a+(1-p)*d).trans (le_max_right _ _)
  · exact (by linarith only [hda] : (a+d)/2 ≤ a).trans (le_max_left _ _)

private theorem sqrt_le_max_weighted {A D p : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hp : p ≤ 1/2) :
    Real.sqrt (A*D) ≤ max A (A^p*D^(1-p)) := by
  have hspos : 0 < Real.sqrt (A*D) := Real.sqrt_pos.mpr (mul_pos hA hD)
  have hBpos : 0 < A^p*D^(1-p) :=
    mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hD _)
  have hs : Real.log (Real.sqrt (A*D)) = (Real.log A+Real.log D)/2 := by
    rw [Real.sqrt_eq_rpow,Real.log_rpow (mul_pos hA hD),Real.log_mul hA.ne' hD.ne']
    ring
  have hB : Real.log (A^p*D^(1-p)) = p*Real.log A+(1-p)*Real.log D := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hA,Real.log_rpow hD]
  rcases le_max_iff.mp (half_le_max_weighted (a := Real.log A) (d := Real.log D) hp)
      with hleft | hright
  · rw [← hs] at hleft
    exact ((Real.log_le_log_iff hspos hA).mp hleft).trans (le_max_left _ _)
  · rw [← hs,← hB] at hright
    exact ((Real.log_le_log_iff hspos hBpos).mp hright).trans (le_max_right _ _)

private theorem two_terms_sqrt_collapse {A D p : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hp : p ≤ 1/2) :
    A+Real.sqrt (A*D) ≤ 2*(A+A^p*D^(1-p)) := by
  have hh := sqrt_le_max_weighted hA hD hp
  have hB : 0 ≤ A^p*D^(1-p) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hD.le _)
  have hm : max A (A^p*D^(1-p)) ≤ A+A^p*D^(1-p) :=
    max_le (le_add_of_nonneg_right hB) (le_add_of_nonneg_left hA.le)
  linarith only [hh,hm,hB]

private theorem physical_weighted_factorization (k : ℕ)
    {β R x H Q m : ℝ} (hβ : 0 < β) (hR : 0 < R) (hx : 0 < x)
    (hH : 0 < H) (hQ : 0 < Q) (hm : 0 < m) :
    let p := 1/((k:ℝ)+1)
    ((β^(k+1)*R/(4*(4*H)^k*Q))*x)^p*(R^2/(2*m))^(1-p) =
      (β*(R^(2-p)/m^(1-p))/(4*(2*H)^(1-p)*Q^p))*x^p := by
  let p := 1/((k:ℝ)+1)
  let A := (β^(k+1)*R/(4*(4*H)^k*Q))*x
  let D := R^2/(2*m)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hlogA : Real.log A = ((k:ℝ)+1)*Real.log β+Real.log R-
      (Real.log 4+(k:ℝ)*(Real.log 4+Real.log H)+Real.log Q)+Real.log x := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) hx.ne',
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hR.ne',Real.log_pow,
      Real.log_mul (by positivity) hQ.ne',
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity),
      Real.log_pow,Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hH.ne']
    push_cast
    ring
  have hlogD : Real.log D = 2*Real.log R-(Real.log 2+Real.log m) := by
    dsimp only [D]
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hm.ne']
    norm_num
  have hlogB : Real.log ((β*(R^(2-p)/m^(1-p))/(4*(2*H)^(1-p)*Q^p))*x^p) =
      Real.log β+(2-p)*Real.log R-(1-p)*Real.log m-
        (Real.log 4+(1-p)*(Real.log 2+Real.log H)+p*Real.log Q)+p*Real.log x := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hx _).ne',
      Real.log_div (by positivity) (by positivity),
      Real.log_mul hβ.ne' (by positivity),
      Real.log_div (Real.rpow_pos_of_pos hR _).ne' (Real.rpow_pos_of_pos hm _).ne',
      Real.log_rpow hR,Real.log_rpow hm,
      Real.log_mul (by positivity) (Real.rpow_pos_of_pos hQ _).ne',
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by positivity : 0 < 2*H),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne',
      Real.log_rpow hQ,Real.log_rpow hx]
    ring
  change A^p*D^(1-p) = _
  apply Real.log_injOn_pos
    (show A^p*D^(1-p) ∈ Set.Ioi 0 from mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hD _))
    (show (β*(R^(2-p)/m^(1-p))/(4*(2*H)^(1-p)*Q^p))*x^p ∈ Set.Ioi 0 from
      Set.mem_Ioi.mpr (by positivity))
  rw [Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hD _).ne',
    Real.log_rpow hA,Real.log_rpow hD,hlogA,hlogD,hlogB]
  have hlog4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hlog4]
  dsimp only [p]
  field_simp
  ring

private theorem physical_square_root_lower {k : ℕ} (hk : 1 ≤ k)
    {β R x H Q m : ℝ} (hβ : 0 < β) (hR : 0 < R) (hx : 0 < x)
    (hH : 0 < H) (hQ : 0 < Q) (hm : 0 < m) :
    let p := 1/((k:ℝ)+1)
    let a := β^(k+1)*R/(4*(4*H)^k*Q)
    let b := β*(R^(2-p)/m^(1-p))/(4*(2*H)^(1-p)*Q^p)
    a*x+Real.sqrt ((a*x)*(R^2/(2*m))) ≤ 2*(a*x+b*x^p) := by
  have hkreal : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 1/((k:ℝ)+1) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
    linarith
  have ha : 0 < (β^(k+1)*R/(4*(4*H)^k*Q))*x := by positivity
  have hd : 0 < R^2/(2*m) := by positivity
  have hh := two_terms_sqrt_collapse ha hd hp
  rw [physical_weighted_factorization k hβ hR hx hH hQ hm] at hh
  exact hh

private theorem actual_square_root_comparison
    {σ τ ν ε η θ ζ : ℝ} (hσ : 3/4 < σ)
    (hν : 0 < ν) (hνhalf : ν ≤ 1/2) (hgap : (τ+1)*ν < 2*σ-3/2)
    (hε : 0 < ε) (hη : 0 < η) (hθ : 0 < θ) (hζ : 0 < ζ) :
    ∃ B C M K δ N₀ : ℝ, 0 < B ∧ 0 < C ∧ 0 < M ∧ 0 < K ∧
      0 < δ ∧ δ ≤ 1 ∧ δ ≤ ζ ∧ 4 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L d : ℝ),
        N₀ ≤ P.N → P.N ≤ L → L ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(σ-δ) ≤ P.V → 0 < d →
        let H := L^ν
        let U := L+H+2
        let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
        let F := 32*C*P.N^2/P.V^2+d^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let J := bourgainZetaBandCount B U 1
        (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F ∨
        ∃ S : Finset ℝ,S ⊆ P.ordinates ∧ S.Nonempty ∧
          (P.ordinates.card:ℝ) ≤ 380*(J:ℝ)*(S.card:ℝ) ∧
          ∃ j ∈ Finset.range J, ∃ k : ℕ,(k = 5 ∨ k = 18) ∧
            let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
            let G := 4*(4*(H+1))^k*Q*(J:ℝ)^(k+1)
            ∃ u ∈ Ioc (-(H+1)) (H+1),
              (bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).Nonempty ∧
              let x := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
              P.V^2*(d^2/G*(S.card:ℝ)*x+
                Real.sqrt ((d^2/G*(S.card:ℝ)*x)*((S.card:ℝ)^2/(2*(I.card:ℝ))))) <
                K*P.N^η*(1+2*Real.pi*P.N^η)*P.T^θ*
                  (Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ))*
                    Real.sqrt (bourgainSecondBudget P.N L x)) := by
  obtain ⟨B,C,M,K,δ,N₀,hB,hC,hM,hK,hδ,hδ1,hδζ,hN₀,hphysical⟩ :=
    actual_power_window_comparison hσ hν hνhalf hgap hε hη hθ hζ
  refine ⟨B,C,M,2*K,δ,N₀,hB,hC,hM,by positivity,hδ,hδ1,hδζ,hN₀,?_⟩
  intro P L d hN hNL hLT hTu hV hd
  rcases hphysical P L d hN hNL hLT hTu hV hd with hs |
    ⟨S,hS,hSne,hpack,j,hj,k,hk,u,hu,hxne,hcomparison⟩
  · exact Or.inl hs
  right
  let H := L^ν
  let U := L+H+2
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let J := bourgainZetaBandCount B U 1
  let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
  let G := 4*(4*(H+1))^k*Q*(J:ℝ)^(k+1)
  let p := 1/((k:ℝ)+1)
  let β := d^(2/((k:ℝ)+1))/(J:ℝ)
  let R := (S.card:ℝ)
  let x := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
  let m := (I.card:ℝ)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hLp : 0 < L := hNp.trans_le hNL
  have hHp : 0 < H+1 := by dsimp only [H]; positivity
  have hJ : (0:ℝ) < J := by exact_mod_cast bourgainZetaBandCount_pos B U 1
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hR : 0 < R := Nat.cast_pos.mpr hSne.card_pos
  have hx : 0 < x := Nat.cast_pos.mpr hxne.card_pos
  have hm : 0 < m := by dsimp only [m,I]; simp only [Finset.card_range]; positivity
  have hβ : 0 < β := div_pos (Real.rpow_pos_of_pos hd _) hJ
  have hk1 : 1 ≤ k := by rcases hk with hh | hh <;> omega
  have hroot : (d^(2/((k:ℝ)+1)))^(k+1) = d^2 := by
    rw [← Real.rpow_mul_natCast hd.le]
    have he : (2/((k:ℝ)+1))*((k+1:ℕ):ℝ) = (2:ℝ) := by
      push_cast
      exact div_mul_cancel₀ 2 (by positivity)
    rw [he,Real.rpow_two]
  have hβpow : β^(k+1) = d^2/(J:ℝ)^(k+1) := by
    dsimp only [β]
    rw [div_pow,hroot]
  have hfirstEq : (β^(k+1)*R/(4*(4*(H+1))^k*Q))*x = d^2/G*R*x := by
    rw [hβpow]
    dsimp only [G]
    field_simp
  have hcollapse := physical_square_root_lower hk1 hβ hR hx hHp hQ hm
  have hleft := mul_le_mul_of_nonneg_left hcollapse (sq_nonneg P.V)
  rw [hfirstEq] at hleft
  have hstrict := mul_lt_mul_of_pos_left hcomparison (by norm_num : (0:ℝ) < 2)
  change 2*(P.V^2*((β^(k+1)*R/(4*(4*(H+1))^k*Q))*x+
    (β*(R^(2-p)/m^(1-p))/(4*(2*(H+1))^(1-p)*Q^p))*x^p)) <
    2*(K*P.N^η*(1+2*Real.pi*P.N^η)*P.T^θ*
      (Real.sqrt (bourgainSecondBudget P.N P.T R)*Real.sqrt (bourgainSecondBudget P.N L x)))
    at hstrict
  rw [hfirstEq] at hstrict
  have hfinal := hleft.trans_lt (by convert hstrict using 1; ring)
  refine ⟨S,hS,hSne,hpack,j,hj,k,hk,u,hu,hxne,?_⟩
  convert hfinal using 1
  ring

private theorem physical_denominator_le {H J : ℝ} {k : ℕ}
    (hH : 1 ≤ H) (hJ : 1 ≤ J) (hk : k ≤ 18) :
    4*(4*(H+1))^k*((2*Nat.ceil (H+1)+1:ℕ):ℝ)*J^(k+1) ≤
      4*(8*H*J)^19 := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ H+1)
  have hQ : ((2*Nat.ceil (H+1)+1:ℕ):ℝ) ≤ 8*H := by
    push_cast
    linarith
  have hbase : 1 ≤ 8*H*J :=
    one_le_mul_of_one_le_of_one_le (by linarith) hJ
  calc
    _ ≤ 4*(8*H)^k*(8*H)*J^(k+1) := by
      have hpow : (4*(H+1))^k ≤ (8*H)^k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hQ
          (by positivity) (by positivity)) (pow_nonneg hJp.le _)
    _ = 4*(8*H*J)^(k+1) := by
      rw [mul_pow (8*H) J (k+1),pow_succ (8*H) k]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) (by norm_num)


private theorem physical_denominator_uniform_power
    {B τ ν κ : ℝ} (hB : 0 < B) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hκ : 0 < κ) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧
      ∀ N L δ : ℝ,N₀ ≤ N → N ≤ L → L ≤ N^(τ+δ) → δ ≤ 1 →
        let H := L^ν
        let U := L+H+2
        let J := (bourgainZetaBandCount B U 1:ℝ)
        J ≤ D*N^κ ∧ ∀ k : ℕ,k ≤ 18 →
          4*(4*(H+1))^k*((2*Nat.ceil (H+1)+1:ℕ):ℝ)*J^(k+1) ≤
            D*N^(19*((|τ|+1)*ν+κ)) := by
  obtain ⟨D₁,N₀,hD₁,hN₀,hcount⟩ := bourgainZetaBandCount_uniform_power
    (A := 0) (u := |τ|+1) hB (by norm_num) (by positivity) hκ
  let D := max D₁ (4*(8*D₁)^19)
  refine ⟨D,N₀,hD₁.trans (le_max_left _ _),hN₀,?_⟩
  intro N L δ hN hNL hLu hδ
  let H := L^ν
  let U := L+H+2
  let J := (bourgainZetaBandCount B U 1:ℝ)
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hL2 : 2 ≤ L := hN2.trans hNL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hH1 : 1 ≤ H := Real.one_le_rpow hL1 hν
  have hHL : H ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 hν1
  have hLcap : L ≤ N^(|τ|+1) := hLu.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self τ]))
  have hU : 0 ≤ U := by dsimp only [U]; linarith
  have hUcap : U ≤ 3*N^(|τ|+1) := by dsimp only [U]; linarith
  have hJbound : J ≤ D₁*N^κ := by
    simpa only [neg_zero,Real.rpow_zero] using hcount N U hN hU hUcap
  have hJ1 : 1 ≤ J := by
    dsimp only [J]
    exact_mod_cast (show 1 ≤ bourgainZetaBandCount B U 1 from bourgainZetaBandCount_pos B U 1)
  have hHbound : H ≤ N^((|τ|+1)*ν) := by
    have hh := Real.rpow_le_rpow hLp.le hLcap hν
    rwa [← Real.rpow_mul hNp.le] at hh
  refine ⟨hJbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNp.le _)),?_⟩
  intro k hk
  calc
    _ ≤ 4*(8*H*J)^19 := physical_denominator_le hH1 hJ1 hk
    _ ≤ 4*(8*N^((|τ|+1)*ν)*(D₁*N^κ))^19 := by gcongr
    _ = (4*(8*D₁)^19)*N^(19*((|τ|+1)*ν+κ)) := by
      have he : 8*N^((|τ|+1)*ν)*(D₁*N^κ) = (8*D₁)*N^((|τ|+1)*ν+κ) := by
        rw [Real.rpow_add hNp]
        ring
      rw [he,mul_pow,← Real.rpow_mul_natCast hNp.le]
      norm_num only [Nat.cast_ofNat]
      rw [mul_comm ((|τ|+1)*ν+κ) 19]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hNp.le _)

private theorem mixed_budget_two_height_log
    {N T L R X K τ τlocal : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hR : 0 < R) (hX : 0 < X) (hK : 0 < K)
    (hTcap : T ≤ N^τ) (hLcap : L ≤ N^τlocal) (a : ℝ) :
    Real.logb N (K*N^a*
      (Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N L X))) ≤
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τlocal (Real.logb N X)/2 := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hBR := bourgainSecondBudget_pos hNp hT hR
  have hBX := bourgainSecondBudget_pos hNp hL hX
  have hRlog := bourgain_budget_log_bound hN hT hR hTcap
  have hXlog := bourgain_budget_log_bound hN hL hX hLcap
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul hK.ne' (Real.rpow_pos_of_pos hNp _).ne',
    Real.logb_rpow hNp hN.ne',
    Real.logb_mul (Real.sqrt_pos.mpr hBR).ne' (Real.sqrt_pos.mpr hBX).ne',
    Real.logb_mul (by norm_num : (3:ℝ) ≠ 0) hK.ne']
  simp only [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hBR,
    Real.logb_rpow_eq_mul_logb_of_pos hBX]
  linarith


private theorem square_root_comparison_log
    {N T L V d G m R X K τ τlocal a : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hV : 0 < V) (hd : 0 < d) (hG : 0 < G) (hm : 0 < m)
    (hR : 0 < R) (hX : 0 < X) (hK : 0 < K)
    (hTcap : T ≤ N^τ) (hLcap : L ≤ N^τlocal)
    (hcomp : V^2*(d^2/G*R*X+Real.sqrt ((d^2/G*R*X)*(R^2/(2*m)))) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N L X))) :
    max (2*Real.logb N V+2*Real.logb N d-Real.logb N G+Real.logb N R+Real.logb N X)
      (2*Real.logb N V+Real.logb N d-Real.logb N G/2+
        3*Real.logb N R/2+Real.logb N X/2-Real.logb N (2*m)/2) <
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τlocal (Real.logb N X)/2 := by
  have hterm : 0 < d^2/G*R*X := by positivity
  have hinside : 0 < (d^2/G*R*X)*(R^2/(2*m)) := by positivity
  have hfirst := (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (sq_nonneg V)).trans_lt hcomp
  have hsecond := (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left hterm.le) (sq_nonneg V)).trans_lt hcomp
  have hlog₁ := Real.logb_lt_logb hN (by positivity) hfirst
  have hlog₂ := Real.logb_lt_logb hN (by positivity) hsecond
  have hbase : Real.logb N (d^2/G*R*X) =
      2*Real.logb N d-Real.logb N G+Real.logb N R+Real.logb N X := by
    rw [Real.logb_mul (by positivity) hX.ne',Real.logb_mul (by positivity) hR.ne',
      Real.logb_div (pow_pos hd 2).ne' hG.ne',Real.logb_pow]
    norm_num
  have hroot : Real.logb N (Real.sqrt ((d^2/G*R*X)*(R^2/(2*m)))) =
      Real.logb N d-Real.logb N G/2+
        3*Real.logb N R/2+Real.logb N X/2-Real.logb N (2*m)/2 := by
    rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hinside,
      Real.logb_mul hterm.ne' (by positivity),hbase,
      Real.logb_div (pow_pos hR 2).ne' (by positivity),Real.logb_pow]
    norm_num
    ring
  rw [Real.logb_mul (pow_pos hV 2).ne' hterm.ne',hbase,Real.logb_pow] at hlog₁
  rw [Real.logb_mul (pow_pos hV 2).ne' (Real.sqrt_pos.mpr hinside).ne',
    hroot,Real.logb_pow] at hlog₂
  norm_num only [Nat.cast_ofNat] at hlog₁ hlog₂
  have hupper := mixed_budget_two_height_log hN hT hL hR hX hK hTcap hLcap a
  exact max_lt (by linarith) (by linarith)

private theorem square_root_power_log
    {N T L V G m R X K D σ τ τlocal δ α χ E a : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hG : 0 < G) (hm : 0 < m) (hR : 0 < R) (hX : 0 < X)
    (hK : 0 < K) (hD : 0 < D)
    (hTcap : T ≤ N^τ) (hLcap : L ≤ N^τlocal)
    (hV : N^(σ-δ) ≤ V) (hGcap : G ≤ D*N^E) (hbin : m ≤ 2*N^χ)
    (hcomp : V^2*((N^(-α))^2/G*R*X+
        Real.sqrt (((N^(-α))^2/G*R*X)*(R^2/(2*m)))) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N L X))) :
    max (2*σ-2*α+Real.logb N R+Real.logb N X-E-2*δ-Real.logb N D)
      (2*σ-α-χ/2+3*Real.logb N R/2+Real.logb N X/2-
        E/2-2*δ-Real.logb N (4*D)/2) <
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τlocal (Real.logb N X)/2 := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hVp : 0 < V := (Real.rpow_pos_of_pos hNp _).trans_le hV
  have hlog := square_root_comparison_log hN hT hL hVp
    (Real.rpow_pos_of_pos hNp _) hG hm hR hX hK hTcap hLcap hcomp
  have hVlog : σ-δ ≤ Real.logb N V :=
    (Real.le_logb_iff_rpow_le hN hVp).mpr hV
  have hGlog : Real.logb N G ≤ Real.logb N D+E := by
    have hh := (Real.logb_le_logb hN hG (by positivity)).mpr hGcap
    rwa [Real.logb_mul hD.ne' (Real.rpow_pos_of_pos hNp _).ne',
      Real.logb_rpow hNp hN.ne'] at hh
  have hmlog : Real.logb N (2*m) ≤ Real.logb N 4+χ := by
    have hh := (Real.logb_le_logb hN (by positivity) (by positivity)).mpr
      (show 2*m ≤ 4*N^χ by linarith)
    rwa [Real.logb_mul (by norm_num : (4:ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hNp _).ne',Real.logb_rpow hNp hN.ne'] at hh
  rw [Real.logb_rpow hNp hN.ne'] at hlog
  have hfirst := (le_max_left _ _).trans_lt hlog
  have hsecond := (le_max_right _ _).trans_lt hlog
  rw [Real.logb_mul (by norm_num : (4:ℝ) ≠ 0) hD.ne']
  exact max_lt (by linarith) (by linarith)


private theorem eliminate_slice_exponent
    {σ α χ r x g τlocal z₁ z₂ w : ℝ}
    (hcomp : max (2*σ-2*α+r+x-z₁)
      (2*σ-α-χ/2+3*r/2+x/2-z₂) <
        w+g+heathBrownDoubleZetaExponent τlocal x/2) :
    r < max (max (g+1/2-2*σ+2*α+z₁+w)
      ((2/3)*(g+1-2*σ+α+χ/2+z₂+w)))
      ((8/11)*(g+1/2+τlocal/4-2*σ+5*α/4+3*χ/8+z₁/4+3*z₂/4+w)) := by
  have h₁ := (le_max_left _ _).trans_lt hcomp
  have h₂ := (le_max_right _ _).trans_lt hcomp
  by_cases hlast : max (2*x+1) (x+2) ≤ 5/4*x+1/2*τlocal+1
  · rw [heathBrownDoubleZetaExponent,max_eq_right hlast] at h₁ h₂
    exact (show r < (8/11)*(g+1/2+τlocal/4-2*σ+5*α/4+3*χ/8+
      z₁/4+3*z₂/4+w) by linarith).trans_le (le_max_right _ _)
  · have hlast' := le_of_not_ge hlast
    rw [heathBrownDoubleZetaExponent,max_eq_left hlast'] at h₁ h₂
    rcases le_total (2*x+1) (x+2) with h | h
    · rw [max_eq_right h] at h₂
      exact (show r < (2/3)*(g+1-2*σ+α+χ/2+z₂+w) by linarith).trans_le
        ((le_max_right _ _).trans (le_max_left _ _))
    · rw [max_eq_left h] at h₁
      exact (show r < g+1/2-2*σ+2*α+z₁+w by linarith).trans_le
        ((le_max_left _ _).trans (le_max_left _ _))

private theorem actual_slice_eliminated_comparison
    {σ τ χ α ν ε η θ κ ζ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hν : 0 < ν) (hνhalf : ν ≤ 1/2) (hgap : (τ+1)*ν < 2*σ-3/2)
    (hε : 0 < ε) (hη : 0 < η) (hθ : 0 < θ) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ C M K D δ N₀ : ℝ, 0 < C ∧ 0 < M ∧ 0 < K ∧ 1 ≤ D ∧
      0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧ δ ≤ ζ ∧ 4 ≤ N₀ ∧
      ∀ P : LargeValuePattern,N₀ ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let L := P.T/P.N^χ
        let H := L^ν
        let U := L+H+2
        let A₀ := 16*C*P.N*Real.sqrt P.N/P.V^2
        let F := 32*C*P.N^2/P.V^2+
          (P.N^(-α))^2*M*(U^(1+ε)*A₀^6+U^(3+ε)*A₀^19)
        let I := Finset.range (Nat.floor (P.T/L)+1)
        (P.ordinates.card:ℝ) ≤ 20*(I.card:ℝ)*F ∨
          ∃ S : Finset ℝ,S ⊆ P.ordinates ∧ S.Nonempty ∧
            (P.ordinates.card:ℝ) ≤ 380*D*P.N^κ*(S.card:ℝ) ∧
            let r := Real.logb P.N (S.card:ℝ)
            let g := heathBrownDoubleZetaExponent (τ+δ) r/2
            let E := 19*((|τ|+1)*ν+κ)
            let z₁ := E+2*δ+Real.logb P.N D
            let z₂ := E/2+2*δ+Real.logb P.N (4*D)/2
            let w := Real.logb P.N (3*K)+2*η+(τ+δ)*θ
            r < max (max (g+1/2-2*σ+2*α+z₁+w)
              ((2/3)*(g+1-2*σ+α+χ/2+z₂+w)))
              ((8/11)*(g+1/2+(τ-χ+δ)/4-2*σ+5*α/4+3*χ/8+
                z₁/4+3*z₂/4+w)) := by
  obtain ⟨B,C,M,K₀,δ₀,N₁,hB,hC,hM,hK₀,hδ₀,hδ₀one,hδ₀ζ,hN₁,hphysical⟩ :=
    actual_square_root_comparison hσ hν hνhalf hgap hε hη hθ hζ
  obtain ⟨D,N₂,hD,hN₂,hden⟩ :=
    physical_denominator_uniform_power (τ := τ) hB hν.le (by linarith) hκ
  let δ := min δ₀ ((τ-χ-1)/2)
  let K := K₀*(1+2*Real.pi)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδmargin : δ ≤ (τ-χ-1)/2 := min_le_right _ _
  have hδone : δ ≤ 1 := hδle.trans hδ₀one
  have hK : 0 < K := mul_pos hK₀ (by positivity)
  refine ⟨C,M,K,D,δ,max N₁ N₂,hC,hM,hK,hD,hδ,hδone,hδmargin,
    hδle.trans hδ₀ζ,hN₁.trans (le_max_left _ _),?_⟩
  intro P hN hTlo hThi hV
  let L := P.T/P.N^χ
  let H := L^ν
  let U := L+H+2
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let E := 19*((|τ|+1)*ν+κ)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNleft : N₁ ≤ P.N := (le_max_left _ _).trans hN
  have hNright : N₂ ≤ P.N := (le_max_right _ _).trans hN
  have hscales := bourgain_subdivision_physical_scales P.one_lt_N hχ
    (by linarith : 1+δ ≤ τ-χ) hTlo hThi
  have hNL : P.N ≤ L := hscales.2.1
  have hLT : L ≤ P.T := hscales.2.2.1
  have hLu : L ≤ P.N^(τ-χ+δ) := hscales.2.2.2.2
  have hLp : 0 < L := hNp.trans_le hNL
  have hThi₀ : P.T ≤ P.N^(τ+δ₀) := hThi.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  have hdenP := hden P.N L δ hNright hNL (hLT.trans hThi) hδone
  rcases hphysical P L (P.N^(-α)) hNleft hNL hLT hThi₀ hV₀
    (Real.rpow_pos_of_pos hNp _) with hs |
      ⟨S,hS,hSne,hpack,j,_hj,k,hk,u,_hu,hxne,hcomparison⟩
  · exact Or.inl hs
  right
  let J := bourgainZetaBandCount B U 1
  let Q := ((2*Nat.ceil (H+1)+1:ℕ):ℝ)
  let G := 4*(4*(H+1))^k*Q*(J:ℝ)^(k+1)
  let R := (S.card:ℝ)
  let X := ((bourgainIntegerSlice (H+1) U ((2:ℝ)^j) u).card:ℝ)
  let m := (I.card:ℝ)
  have hR : 0 < R := Nat.cast_pos.mpr hSne.card_pos
  have hX : 0 < X := Nat.cast_pos.mpr hxne.card_pos
  have hm : 0 < m := by dsimp only [m,I]; simp only [Finset.card_range]; positivity
  have hJp : (0:ℝ) < J := by exact_mod_cast bourgainZetaBandCount_pos B U 1
  have hQp : 0 < Q := by dsimp only [Q]; positivity
  have hHp : 0 < H+1 := by dsimp only [H]; positivity
  have hGp : 0 < G := by dsimp only [G]; positivity
  have hk18 : k ≤ 18 := by rcases hk with hh | hh <;> omega
  have hGcap : G ≤ D*P.N^E := hdenP.2 k hk18
  have hbin : m ≤ 2*P.N^χ :=
    bourgain_subdivision_bin_count P.one_lt_N.le P.T_pos hχ
  have hpacking : (P.ordinates.card:ℝ) ≤ 380*D*P.N^κ*R := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdenP.1 (by norm_num : (0:ℝ) ≤ 380)) hR.le
    calc
      _ ≤ 380*(J:ℝ)*R := hpack
      _ ≤ 380*(D*P.N^κ)*R := hh
      _ = _ := by ring
  have hfactor : K₀*P.N^η*(1+2*Real.pi*P.N^η)*P.T^θ ≤
      K*P.N^(2*η+(τ+δ)*θ) := by
    have hh := bourgain_integration_power_factor
      (M := K₀) (D := 1/2) P.one_lt_N.le P.T_pos.le hη.le hθ.le hK₀.le
        (by norm_num) hThi
    dsimp only [K]
    convert hh using 1 <;> ring
  have hbudget : 0 ≤ Real.sqrt (bourgainSecondBudget P.N P.T R)*
      Real.sqrt (bourgainSecondBudget P.N L X) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcomp : P.V^2*((P.N^(-α))^2/G*R*X+
      Real.sqrt (((P.N^(-α))^2/G*R*X)*(R^2/(2*m)))) <
      K*P.N^(2*η+(τ+δ)*θ)*
        (Real.sqrt (bourgainSecondBudget P.N P.T R)*
          Real.sqrt (bourgainSecondBudget P.N L X)) :=
    hcomparison.trans_le (mul_le_mul_of_nonneg_right hfactor hbudget)
  have hlog := square_root_power_log P.one_lt_N P.T_pos.le hLp.le
    hGp hm hR hX hK (zero_lt_one.trans_le hD) hThi hLu hV hGcap hbin hcomp
  have hnormalized :
      max (2*σ-2*α+Real.logb P.N R+Real.logb P.N X-
        (E+2*δ+Real.logb P.N D))
        (2*σ-α-χ/2+3*Real.logb P.N R/2+Real.logb P.N X/2-
          (E/2+2*δ+Real.logb P.N (4*D)/2)) <
        (Real.logb P.N (3*K)+2*η+(τ+δ)*θ)+
          heathBrownDoubleZetaExponent (τ+δ) (Real.logb P.N R)/2+
          heathBrownDoubleZetaExponent (τ-χ+δ) (Real.logb P.N X)/2 := by
    convert hlog using 2 <;> ring
  exact ⟨S,hS,hSne,hpacking,eliminate_slice_exponent hnormalized⟩

private theorem three_positive_sum_log {N a b c : ℝ}
    (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.logb N (a+b+c) ≤ Real.logb N 3+
      max (max (Real.logb N a) (Real.logb N b)) (Real.logb N c) := by
  let e := max (max (Real.logb N a) (Real.logb N b)) (Real.logb N c)
  have ha' : a ≤ N^e := (Real.logb_le_iff_le_rpow hN ha).mp
    ((le_max_left _ _).trans (le_max_left _ _))
  have hb' : b ≤ N^e := (Real.logb_le_iff_le_rpow hN hb).mp
    ((le_max_right _ _).trans (le_max_left _ _))
  have hc' : c ≤ N^e := (Real.logb_le_iff_le_rpow hN hc).mp (le_max_right _ _)
  have hh := Real.logb_le_logb_of_le hN (by positivity : 0 < a+b+c)
    (show a+b+c ≤ 3*N^e by linarith)
  rwa [Real.logb_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _).ne',
    Real.logb_rpow (zero_lt_one.trans hN) hN.ne'] at hh


private theorem small_component_logarithm
    {N V U m Q C M σ τ χ α δ ε : ℝ}
    (hN : 1 < N) (hU : 0 < U) (hm : 0 < m) (hQ : 0 < Q)
    (hC : 0 < C) (hM : 0 < M) (hε : 0 ≤ ε)
    (hV : N^(σ-δ) ≤ V) (hUcap : U ≤ 3*N^(τ-χ+δ)) (hbin : m ≤ 2*N^χ)
    (hsmall : Q ≤ 20*m*(32*C*N^2/V^2+
      (N^(-α))^2*M*(U^(1+ε)*(16*C*N*Real.sqrt N/V^2)^6+
        U^(3+ε)*(16*C*N*Real.sqrt N/V^2)^19))) :
    Real.logb N Q ≤ Real.logb N 120+
      max (max (Real.logb N (32*C)+χ+2-2*σ+2*δ)
        (Real.logb N M+(1+ε)*Real.logb N 3+6*Real.logb N (16*C)-
          2*α+τ+9-12*σ+(τ-χ+δ)*ε+13*δ))
        (Real.logb N M+(3+ε)*Real.logb N 3+19*Real.logb N (16*C)-
          2*α+3*τ-2*χ+57/2-38*σ+(τ-χ+δ)*ε+41*δ) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hVp : 0 < V := (Real.rpow_pos_of_pos hNp _).trans_le hV
  let A := 16*C*N*Real.sqrt N/V^2
  let d := N^(-α)
  let t₀ := 32*C*N^2/V^2
  let t₁ := d^2*M*U^(1+ε)*A^6
  let t₂ := d^2*M*U^(3+ε)*A^19
  have hA : 0 < A := by dsimp only [A]; positivity
  have hd : 0 < d := Real.rpow_pos_of_pos hNp _
  have ht₀ : 0 < t₀ := by dsimp only [t₀]; positivity
  have ht₁ : 0 < t₁ := by dsimp only [t₁]; positivity
  have ht₂ : 0 < t₂ := by dsimp only [t₂]; positivity
  have hVlog : σ-δ ≤ Real.logb N V :=
    (Real.le_logb_iff_rpow_le hN hVp).mpr hV
  have hUlog : Real.logb N U ≤ Real.logb N 3+(τ-χ+δ) := by
    have hh := Real.logb_le_logb_of_le hN hU hUcap
    rwa [Real.logb_mul (by norm_num : (3:ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hNp _).ne',Real.logb_rpow hNp hN.ne'] at hh
  have hmlog : Real.logb N m ≤ Real.logb N 2+χ := by
    have hh := Real.logb_le_logb_of_le hN hm hbin
    rwa [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hNp _).ne',Real.logb_rpow hNp hN.ne'] at hh
  have hAlog : Real.logb N A = Real.logb N (16*C)+3/2-2*Real.logb N V := by
    dsimp only [A]
    rw [Real.logb_div (by positivity) (pow_pos hVp 2).ne',
      Real.logb_mul (by positivity) (Real.sqrt_pos.mpr hNp).ne',
      Real.logb_mul (by positivity) hNp.ne',Real.sqrt_eq_rpow,
      Real.logb_rpow_eq_mul_logb_of_pos hNp,Real.logb_pow,
      Real.logb_self_eq_one hN]
    norm_num
    ring
  have ht₀log : Real.logb N t₀ = Real.logb N (32*C)+2-2*Real.logb N V := by
    dsimp only [t₀]
    rw [Real.logb_div (by positivity) (pow_pos hVp 2).ne',
      Real.logb_mul (by positivity) (pow_pos hNp 2).ne',
      Real.logb_pow,Real.logb_pow,Real.logb_self_eq_one hN]
    norm_num
  have hmoment (q : ℕ) (b : ℝ) :
      Real.logb N (d^2*M*U^b*A^q) =
        -2*α+Real.logb N M+b*Real.logb N U+(q:ℝ)*Real.logb N A := by
    rw [Real.logb_mul (by positivity) (pow_pos hA q).ne',
      Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hU b).ne',
      Real.logb_mul (pow_pos hd 2).ne' hM.ne',Real.logb_pow,Real.logb_pow,
      Real.logb_rpow_eq_mul_logb_of_pos hU]
    dsimp only [d]
    rw [Real.logb_rpow hNp hN.ne']
    norm_num
  have hsum := three_positive_sum_log hN ht₀ ht₁ ht₂
  have htotal : Q ≤ 20*m*(t₀+t₁+t₂) := by
    convert hsmall using 1
    dsimp only [t₀,t₁,t₂,A,d]
    ring
  have hQlog := Real.logb_le_logb_of_le hN hQ htotal
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by norm_num : (20:ℝ) ≠ 0) hm.ne'] at hQlog
  have h₀ : χ+Real.logb N t₀ ≤ Real.logb N (32*C)+χ+2-2*σ+2*δ := by
    rw [ht₀log]
    linarith
  have h₁ : χ+Real.logb N t₁ ≤
      Real.logb N M+(1+ε)*Real.logb N 3+6*Real.logb N (16*C)-
        2*α+τ+9-12*σ+(τ-χ+δ)*ε+13*δ := by
    dsimp only [t₁]
    rw [hmoment,hAlog]
    norm_num only [Nat.cast_ofNat]
    have hu := mul_le_mul_of_nonneg_left hUlog (by linarith : 0 ≤ 1+ε)
    linarith
  have h₂ : χ+Real.logb N t₂ ≤
      Real.logb N M+(3+ε)*Real.logb N 3+19*Real.logb N (16*C)-
        2*α+3*τ-2*χ+57/2-38*σ+(τ-χ+δ)*ε+41*δ := by
    dsimp only [t₂]
    rw [hmoment,hAlog]
    norm_num only [Nat.cast_ofNat]
    have hu := mul_le_mul_of_nonneg_left hUlog (by linarith : 0 ≤ 3+ε)
    linarith
  have hmax := max_le_max (max_le_max h₀ h₁) h₂
  rw [max_add_add_left,max_add_add_left] at hmax
  have hconstant : Real.logb N 120 = Real.logb N 20+Real.logb N 2+Real.logb N 3 := by
    rw [show (120:ℝ) = (20*2)*3 by norm_num,
      Real.logb_mul (by norm_num : (20*2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0),
      Real.logb_mul (by norm_num : (20:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  rw [hconstant]
  linarith

private theorem actual_uniform_logarithmic_alternative
    {σ τ χ α ν t : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hν : 0 < ν) (hνhalf : ν ≤ 1/2) (hνt : ν ≤ t)
    (hgap : (τ+1)*ν < 2*σ-3/2) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ δ N₀ : ℝ,0 < δ ∧ δ ≤ t ∧ 4 ≤ N₀ ∧
      ∀ P : LargeValuePattern,P.ordinates.Nonempty → N₀ ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let q := Real.logb P.N (P.ordinates.card:ℝ)
        let s := max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
          (-2*α+3*τ-2*χ+57/2-38*σ)
        q ≤ s+(|τ-χ|+67)*t ∨
          ∃ S : Finset ℝ,S ⊆ P.ordinates ∧ S.Nonempty ∧
            let r := Real.logb P.N (S.card:ℝ)
            r ≤ q ∧ q ≤ r+2*t ∧
            let g := heathBrownDoubleZetaExponent τ r/2
            r ≤ max (max (g+1/2-2*σ+2*α)
              ((2/3)*(g+1-2*σ+α+χ/2)))
              ((8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8))+
                40*(|τ|+3)*t := by
  obtain ⟨C,M,K,D,δ,N₁,hC,hM,hK,hD,hδ,hδ1,hδmargin,hδt,hN₁,hfinite⟩ :=
    actual_slice_eliminated_comparison (α := α) hσ hχ hmargin hν hνhalf hgap ht ht ht ht ht
  let A : Fin 9 → ℝ := ![120,32*C,M,3,16*C,D,4*D,3*K,380*D]
  let B := ∑ i,Real.exp (|Real.log (A i)|/t+1)
  refine ⟨δ,max N₁ B,hδ,hδt,hN₁.trans (le_max_left _ _),?_⟩
  intro P hP hN hTlo hThi hV
  have hNleft : N₁ ≤ P.N := (le_max_left _ _).trans hN
  have hNright : B ≤ P.N := (le_max_right _ _).trans hN
  have hlogs (i : Fin 9) : Real.logb P.N (A i) ≤ t :=
    (le_abs_self _).trans (bourgain_abs_logb_le_of_sum_threshold
      A P.one_lt_N ht hNright i)
  have h120 : Real.logb P.N 120 ≤ t := hlogs 0
  have h32C : Real.logb P.N (32*C) ≤ t := hlogs 1
  have hMlog : Real.logb P.N M ≤ t := hlogs 2
  have h3 : Real.logb P.N 3 ≤ t := hlogs 3
  have h16C : Real.logb P.N (16*C) ≤ t := hlogs 4
  have hDlog : Real.logb P.N D ≤ t := hlogs 5
  have h4D : Real.logb P.N (4*D) ≤ t := hlogs 6
  have h3K : Real.logb P.N (3*K) ≤ t := hlogs 7
  have h380D : Real.logb P.N (380*D) ≤ t := hlogs 8
  let s := max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
    (-2*α+3*τ-2*χ+57/2-38*σ)
  have hs₀ : χ+2-2*σ ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hs₁ : -2*α+τ+9-12*σ ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have hs₂ : -2*α+3*τ-2*χ+57/2-38*σ ≤ s := le_max_right _ _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hQ : (0:ℝ) < P.ordinates.card := Nat.cast_pos.mpr hP.card_pos
  rcases hfinite P hNleft hTlo hThi hV with hsmall | ⟨S,hS,hSne,hpack,hlarge⟩
  · left
    let L := P.T/P.N^χ
    let H := L^ν
    let U := L+H+2
    let I := Finset.range (Nat.floor (P.T/L)+1)
    have hscales := bourgain_subdivision_physical_scales P.one_lt_N hχ
      (by linarith : 1+δ ≤ τ-χ) hTlo hThi
    have hNL : P.N ≤ L := hscales.2.1
    have hLu : L ≤ P.N^(τ-χ+δ) := hscales.2.2.2.2
    have hL4 : 4 ≤ L := (hN₁.trans hNleft).trans hNL
    have hLp : 0 < L := by linarith
    have hHL : H ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by linarith : ν ≤ 1)
    have hHp : 0 < H := Real.rpow_pos_of_pos hLp _
    have hU : 0 < U := by dsimp only [U]; linarith
    have hUcap : U ≤ 3*P.N^(τ-χ+δ) := by dsimp only [U]; linarith
    have hm : (0:ℝ) < I.card := by dsimp only [I]; simp only [Finset.card_range]; positivity
    have hbin : (I.card:ℝ) ≤ 2*P.N^χ :=
      bourgain_subdivision_bin_count P.one_lt_N.le P.T_pos hχ
    have hl := small_component_logarithm P.one_lt_N hU hm hQ hC hM ht.le
      hV hUcap hbin hsmall
    have hlocal := mul_le_mul_of_nonneg_right
      (show τ-χ+δ ≤ |τ-χ|+1 by linarith [le_abs_self (τ-χ)]) ht.le
    have hu₁ : (1+t)*Real.logb P.N 3 ≤ 2*t := by
      have hh := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ 1+t)
      nlinarith only [hh,ht.le,ht1]
    have hu₃ : (3+t)*Real.logb P.N 3 ≤ 4*t := by
      have hh := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ 3+t)
      nlinarith only [hh,ht.le,ht1]
    have hb₀ : Real.logb P.N (32*C)+χ+2-2*σ+2*δ ≤ s+(|τ-χ|+66)*t := by
      nlinarith only [h32C,hs₀,hδt,ht.le,abs_nonneg (τ-χ)]
    have hb₁ : Real.logb P.N M+(1+t)*Real.logb P.N 3+6*Real.logb P.N (16*C)-
        2*α+τ+9-12*σ+(τ-χ+δ)*t+13*δ ≤ s+(|τ-χ|+66)*t := by
      nlinarith only [hMlog,hu₁,h16C,hs₁,hlocal,hδt,ht.le]
    have hb₂ : Real.logb P.N M+(3+t)*Real.logb P.N 3+19*Real.logb P.N (16*C)-
        2*α+3*τ-2*χ+57/2-38*σ+(τ-χ+δ)*t+41*δ ≤ s+(|τ-χ|+66)*t := by
      nlinarith only [hMlog,hu₃,h16C,hs₂,hlocal,hδt]
    have hh := max_le (max_le hb₀ hb₁) hb₂
    linarith
  · right
    let r := Real.logb P.N (S.card:ℝ)
    let g := heathBrownDoubleZetaExponent τ r/2
    let gδ := heathBrownDoubleZetaExponent (τ+δ) r/2
    let E := 19*((|τ|+1)*ν+t)
    let z₁ := E+2*δ+Real.logb P.N D
    let z₂ := E/2+2*δ+Real.logb P.N (4*D)/2
    let w := Real.logb P.N (3*K)+2*t+(τ+δ)*t
    let b := max (max (g+1/2-2*σ+2*α)
      ((2/3)*(g+1-2*σ+α+χ/2)))
      ((8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8))
    have hR : (0:ℝ) < S.card := Nat.cast_pos.mpr hSne.card_pos
    have hrle : r ≤ Real.logb P.N (P.ordinates.card:ℝ) :=
      Real.logb_le_logb_of_le P.one_lt_N hR
        (by exact_mod_cast Finset.card_le_card hS)
    have hpacking : Real.logb P.N (P.ordinates.card:ℝ) ≤ r+2*t := by
      have hh := Real.logb_le_logb_of_le P.one_lt_N hQ hpack
      rw [Real.logb_mul (by positivity) hR.ne',
        Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hNp _).ne',
        Real.logb_rpow hNp P.one_lt_N.ne'] at hh
      linarith only [hh,h380D]
    have hE : E ≤ 19*(|τ|+2)*t := by
      have hh := mul_le_mul_of_nonneg_left hνt (by positivity : 0 ≤ |τ|+1)
      dsimp only [E]
      nlinarith only [hh]
    have hz₁ : z₁ ≤ (19*|τ|+41)*t := by
      dsimp only [z₁]
      nlinarith only [hE,hδt,hDlog]
    have hz₂ : z₂ ≤ (19*|τ|/2+43/2)*t := by
      dsimp only [z₂]
      nlinarith only [hE,hδt,h4D]
    have hw : w ≤ (|τ|+4)*t := by
      have hh := mul_le_mul_of_nonneg_right
        (show τ+δ ≤ |τ|+1 by linarith [le_abs_self τ]) ht.le
      dsimp only [w]
      nlinarith only [h3K,hh]
    have hg : gδ ≤ g+t/4 := by
      have hh := bourgain_doubleZeta_height_slack (τ := τ) (r := r) hδ.le
      dsimp only [gδ,g]
      linarith only [hh,hδt]
    have hb₀ : g+1/2-2*σ+2*α ≤ b := (le_max_left _ _).trans (le_max_left _ _)
    have hb₁ : (2/3)*(g+1-2*σ+α+χ/2) ≤ b :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hb₂ : (8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8) ≤ b :=
      le_max_right _ _
    have ha := mul_nonneg (abs_nonneg τ) ht.le
    have hc₀ : gδ+1/2-2*σ+2*α+z₁+w ≤ b+40*(|τ|+3)*t := by
      nlinarith only [hg,hz₁,hw,hb₀,ha,ht.le]
    have hc₁ : (2/3)*(gδ+1-2*σ+α+χ/2+z₂+w) ≤ b+40*(|τ|+3)*t := by
      nlinarith only [hg,hz₂,hw,hb₁,ha,ht.le]
    have hc₂ : (8/11)*(gδ+1/2+(τ-χ+δ)/4-2*σ+5*α/4+3*χ/8+
        z₁/4+3*z₂/4+w) ≤ b+40*(|τ|+3)*t := by
      nlinarith only [hg,hz₁,hz₂,hw,hb₂,hδt,ha,ht.le]
    exact ⟨S,hS,hSne,hrle,hpacking,hlarge.le.trans (max_le (max_le hc₀ hc₁) hc₂)⟩

private theorem region_zero_loss_dichotomy
    {σ τ χ α ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    ρ ≤ max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
      (-2*α+3*τ-2*χ+57/2-38*σ) ∨
      let g := heathBrownDoubleZetaExponent τ ρ/2
      ρ ≤ max (max (g+1/2-2*σ+2*α)
        ((2/3)*(g+1-2*σ+α+χ/2)))
        ((8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8)) := by
  let s := max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
    (-2*α+3*τ-2*χ+57/2-38*σ)
  by_cases hs : ρ ≤ s
  · exact Or.inl hs
  right
  have hsgap : s < ρ := lt_of_not_ge hs
  let c := (2*σ-3/2)/(2*(|τ|+1))
  let ν : ℕ → ℝ := fun n => min (poweringAccuracy n) c
  have hc : 0 < c := div_pos (by linarith only [hσ]) (by positivity)
  have hν (n : ℕ) : 0 < ν n := lt_min (poweringAccuracy_pos n) hc
  have hνt (n : ℕ) : ν n ≤ poweringAccuracy n := min_le_left _ _
  have hνhalf (n : ℕ) : ν n ≤ 1/2 :=
    (hνt n).trans ((poweringAccuracy_le n).trans (by norm_num))
  have hgap (n : ℕ) : (τ+1)*ν n < 2*σ-3/2 := by
    have hv : ν n ≤ c := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(|τ|+1))).mp hv
    have hτ := mul_le_mul_of_nonneg_right
      (show τ+1 ≤ |τ|+1 by linarith only [le_abs_self τ]) (hν n).le
    linarith only [hh,hτ,hσ]
  have he1 (n : ℕ) : poweringAccuracy n ≤ 1 :=
    (poweringAccuracy_le n).trans (by norm_num)
  have hex (n : ℕ) := actual_uniform_logarithmic_alternative (α := α)
    hσ hχ hmargin (hν n) (hνhalf n) (hνt n) (hgap n) (poweringAccuracy_pos n) (he1 n)
  choose δ N₀ hδ hδt hN₀ hf using hex
  obtain ⟨P,_hNtop,hsource,hP⟩ := exists_bourgain_region_family hregion δ N₀ hδ
  have hsmallLimit : Filter.Tendsto
      (fun n => s+(|τ-χ|+67)*poweringAccuracy n) Filter.atTop (nhds s) := by
    simpa only [mul_zero,add_zero] using
      (poweringAccuracy_tendsto.const_mul (|τ-χ|+67)).const_add s
  obtain ⟨n₀,hn₀⟩ := (hsmallLimit.eventually_lt hsource hsgap).exists_forall_of_atTop
  let b : ℝ → ℝ := fun r =>
    let g := heathBrownDoubleZetaExponent τ r/2
    max (max (g+1/2-2*σ+2*α) ((2/3)*(g+1-2*σ+α+χ/2)))
      ((8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8))
  have hlarge (n : ℕ) :
      ∃ S : Finset ℝ,S ⊆ (P (n+n₀)).ordinates ∧ S.Nonempty ∧
        let r := Real.logb (P (n+n₀)).N (S.card:ℝ)
        r ≤ Real.logb (P (n+n₀)).N ((P (n+n₀)).ordinates.card:ℝ) ∧
        Real.logb (P (n+n₀)).N ((P (n+n₀)).ordinates.card:ℝ) ≤
          r+2*poweringAccuracy (n+n₀) ∧
        r ≤ b r+40*(|τ|+3)*poweringAccuracy (n+n₀) := by
    have halt := hf (n+n₀) (P (n+n₀)) (hP (n+n₀)).2.2.2.2.2.1
      (hP (n+n₀)).2.1 (hP (n+n₀)).2.2.1
      (hP (n+n₀)).2.2.2.1 (hP (n+n₀)).2.2.2.2.1
    rcases halt with hsmall | hlarge
    · have hstrict := hn₀ (n+n₀) (Nat.le_add_left _ _)
      exact False.elim (not_le_of_gt hstrict hsmall)
    · exact hlarge
  choose S _hsub _hSne hrle hpack hcomp using hlarge
  let r : ℕ → ℝ := fun n => Real.logb (P (n+n₀)).N ((S n).card:ℝ)
  have hsource' := hsource.comp (Filter.tendsto_add_atTop_nat n₀)
  have he := poweringAccuracy_tendsto.comp (Filter.tendsto_add_atTop_nat n₀)
  have hr : Filter.Tendsto r Filter.atTop (nhds ρ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Filter.Tendsto (fun n =>
          Real.logb (P (n+n₀)).N ((P (n+n₀)).ordinates.card:ℝ)-
            2*poweringAccuracy (n+n₀)) Filter.atTop (nhds ρ) from
        by simpa only [mul_zero,sub_zero] using hsource'.sub (he.const_mul 2))
      hsource'
    · intro n
      have hh := hpack n
      linarith only [hh]
    · exact hrle
  have hb : Continuous b := by
    dsimp only [b]
    unfold heathBrownDoubleZetaExponent
    fun_prop
  have hright : Filter.Tendsto
      (fun n => b (r n)+40*(|τ|+3)*poweringAccuracy (n+n₀))
      Filter.atTop (nhds (b ρ)) := by
    simpa only [mul_zero,add_zero] using
      ((hb.tendsto ρ).comp hr).add (he.const_mul (40*(|τ|+3)))
  exact le_of_tendsto_of_tendsto hr hright (Filter.Eventually.of_forall hcomp)

private theorem cdv_global_budget
    {σ u r : ℝ} (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr1 : r ≤ 1)
    (hr0 : 3*(1-σ)*u ≤ r) :
    heathBrownDoubleZetaExponent (u*(30*σ-11)/8) r/2 ≤
      1+5*r/8+u*(30*σ-27)/32 := by
  have hneg : 0 ≤ 27-30*σ := by linarith only [hσhi]
  have hprod := mul_nonneg (sub_nonneg.mpr hu1) hneg
  have hz : -1 ≤ u*(30*σ-27) := by nlinarith only [hprod,hσ]
  have hpos := mul_nonneg hu0 (show 0 ≤ 18*σ-15 by linarith only [hσ])
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  unfold heathBrownDoubleZetaExponent
  exact max_le (max_le (by nlinarith only [hr1,hz])
    (by nlinarith only [hr0,hpos])) (by nlinarith only [hu1])


private theorem cdv_parameter_budgets
    {σ u : ℝ} (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174)
    (hu : 2/3 ≤ u) (hu1 : u ≤ 1) :
    let τ := u*(30*σ-11)/8
    let r₀ := 3*(1-σ)*u
    let χ := (1-σ)*(3*u-2)
    let α := max ((260-336*σ+u*(162*σ-105))/16)
      ((72-96*σ+u*(54*σ-35))/16)
    let h := u*(30*σ-27)/32
    0 ≤ χ ∧ 1 < τ-χ ∧
      max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
        (-2*α+3*τ-2*χ+57/2-38*σ) ≤ r₀ ∧
      (16/3)*α+(4/3)*(3-4*σ)+(8/3)*h ≤ r₀ ∧
      (8/7)*α+(4/7)*χ+(16/7)*(1-σ)+(8/7)*h ≤ r₀ ∧
      (5/3)*α+χ/6+(2/3)*(3-4*σ)+τ/3+(4/3)*h ≤ r₀ := by
  let τ := u*(30*σ-11)/8
  let r₀ := 3*(1-σ)*u
  let χ := (1-σ)*(3*u-2)
  let a := (260-336*σ+u*(162*σ-105))/16
  let b := (72-96*σ+u*(54*σ-35))/16
  let α := max a b
  let h := u*(30*σ-27)/32
  have hχ : 0 ≤ χ := mul_nonneg (by linarith only [hσhi]) (by linarith only [hu])
  have hmargin : 1 < τ-χ := by
    have hp := mul_nonneg (show 0 ≤ u-2/3 by linarith only [hu])
      (show 0 ≤ 54*σ-35 by linarith only [hσ])
    dsimp only [τ,χ]
    nlinarith only [hp,hσ]
  have ha : a ≤ α := le_max_left _ _
  have hb : b ≤ α := le_max_right _ _
  have hsmall : max (max (χ+2-2*σ) (-2*α+τ+9-12*σ))
      (-2*α+3*τ-2*χ+57/2-38*σ) ≤ r₀ := by
    apply max_le
    · apply max_le
      · dsimp only [χ,r₀]; ring_nf; exact le_rfl
      · dsimp only [b,τ,r₀] at hb ⊢; nlinarith only [hb]
    · dsimp only [a,τ,χ,r₀] at ha ⊢; nlinarith only [ha]
  have budgetA :
      (16/3)*a+(4/3)*(3-4*σ)+(8/3)*h ≤ r₀ ∧
      (8/7)*a+(4/7)*χ+(16/7)*(1-σ)+(8/7)*h ≤ r₀ ∧
      (5/3)*a+χ/6+(2/3)*(3-4*σ)+τ/3+(4/3)*h ≤ r₀ := by
    have hp₁ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 238*σ-161 by linarith only [hσ])
    have hp₂ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 390*σ-273 by linarith only [hσ])
    have hp₃ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 1050*σ-721 by linarith only [hσ])
    dsimp only [a,h,r₀,χ,τ]
    exact ⟨by nlinarith only [hp₁,hσ],by nlinarith only [hp₂,hσ],
      by nlinarith only [hp₃,hσ]⟩
  have budgetB :
      (16/3)*b+(4/3)*(3-4*σ)+(8/3)*h ≤ r₀ ∧
      (8/7)*b+(4/7)*χ+(16/7)*(1-σ)+(8/7)*h ≤ r₀ ∧
      (5/3)*b+χ/6+(2/3)*(3-4*σ)+τ/3+(4/3)*h ≤ r₀ := by
    have hp₁ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 282*σ-203 by linarith only [hσ])
    have hp₂ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 174*σ-133 by linarith only [hσ])
    have hp₃ := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ 510*σ-371 by linarith only [hσ])
    dsimp only [b,h,r₀,χ,τ]
    exact ⟨by nlinarith only [hp₁,hσ],by nlinarith only [hp₂,hσ],
      by nlinarith only [hp₃,hσ]⟩
  refine ⟨hχ,hmargin,hsmall,?_⟩
  change (16/3)*α+(4/3)*(3-4*σ)+(8/3)*h ≤ r₀ ∧
    (8/7)*α+(4/7)*χ+(16/7)*(1-σ)+(8/7)*h ≤ r₀ ∧
    (5/3)*α+χ/6+(2/3)*(3-4*σ)+τ/3+(4/3)*h ≤ r₀
  rcases le_total a b with hh | hh
  · simpa only [α,max_eq_right hh] using budgetB
  · simpa only [α,max_eq_left hh] using budgetA

private theorem cdv_region_cardinality {σ u ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ (u*(30*σ-11)/8) ρ energy)
    (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174)
    (hu : 2/3 ≤ u) (hu1 : u ≤ 1) (hρ1 : ρ ≤ 1) :
    ρ ≤ 3*(1-σ)*u := by
  let τ := u*(30*σ-11)/8
  let r₀ := 3*(1-σ)*u
  let χ := (1-σ)*(3*u-2)
  let α := max ((260-336*σ+u*(162*σ-105))/16)
    ((72-96*σ+u*(54*σ-35))/16)
  let h := u*(30*σ-27)/32
  let g := heathBrownDoubleZetaExponent τ ρ/2
  obtain ⟨hχ,hmargin,hsmall,hfirst,hsecond,hthird⟩ := cdv_parameter_budgets hσ hσhi hu hu1
  have hσ' : 3/4 < σ := by linarith only [hσ]
  have hd := region_zero_loss_dichotomy (χ := χ) (α := α) hregion hσ' hχ hmargin
  rcases hd with hs | hl
  · exact hs.trans hsmall
  by_cases hρ : ρ ≤ r₀
  · exact hρ
  have hg : g ≤ 1+5*ρ/8+h :=
    cdv_global_budget hσ hσhi (by linarith only [hu]) hu1 hρ1 (le_of_not_ge hρ)
  change ρ ≤ max (max (g+1/2-2*σ+2*α)
    ((2/3)*(g+1-2*σ+α+χ/2)))
    ((8/11)*(g+1/2+(τ-χ)/4-2*σ+5*α/4+3*χ/8)) at hl
  rcases le_max_iff.mp hl with h12 | h3
  · rcases le_max_iff.mp h12 with h1 | h2
    · have hh : ρ ≤ (16/3)*α+(4/3)*(3-4*σ)+(8/3)*h := by linarith only [hg,h1]
      exact hh.trans hfirst
    · have hh : ρ ≤ (8/7)*α+(4/7)*χ+(16/7)*(1-σ)+(8/7)*h := by
        linarith only [hg,h2]
      exact hh.trans hsecond
  · have hh : ρ ≤ (5/3)*α+χ/6+(2/3)*(3-4*σ)+τ/3+(4/3)*h := by
      linarith only [hg,h3]
    exact hh.trans hthird


private theorem cdv_largeValueExponent {σ u : ℝ}
    (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174)
    (hu : 2/3 ≤ u) (hu1 : u ≤ 1) :
    largeValueExponent σ (u*(30*σ-11)/8) ≤ ((3*(1-σ)*u:ℝ):EReal) := by
  let τ := u*(30*σ-11)/8
  have hden : 0 < 30*σ-11 := by linarith only [hσ]
  have hτ : 0 < τ := div_pos (mul_pos (by linarith only [hu]) hden) (by norm_num)
  have hτhi : τ ≤ (30*σ-11)/8 := by
    have hh := mul_le_mul_of_nonneg_right hu1 hden.le
    dsimp only [τ]
    linarith only [hh]
  have hhalf : 1/2 ≤ σ := by linarith only [hσ]
  have hone : σ ≤ 1 := by linarith only [hσhi]
  have hgap : τ/8 < 2*σ-3/2 := by linarith only [hτhi,hσ]
  have hbound := largeValueExponent_le_of_bound (ivicNineteenth_general_largeValueBound hτ hgap)
  have hmax : max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ)) ≤ 1 :=
    max_le (by linarith only [hσ])
      (max_le (by linarith only [hτhi,hσ]) (by linarith only [hτhi,hσ]))
  have hcoe := largeValueExponent_coe_toReal hhalf hone hτ.le
  have hρ1 : (largeValueExponent σ τ).toReal ≤ 1 := by
    have hh := hbound.trans (EReal.coe_le_coe_iff.mpr hmax)
    rw [← hcoe] at hh
    exact EReal.coe_le_coe_iff.mp hh
  obtain ⟨e,s,hm⟩ := exists_energyRegion_at_largeValueExponent hhalf hone hτ.le
  have hh := cdv_region_cardinality
    (show InCardinalityEnergyRegion σ τ (largeValueExponent σ τ).toReal e from ⟨s,hm⟩)
    hσ hσhi hu hu1 hρ1
  rw [← hcoe]
  exact EReal.coe_le_coe_iff.mpr hh

/-- The mixed sixth/nineteenth-power large-value bound on the complete
closed two-thirds transfer interval, derived from actual region realizations. -/
theorem cdv_largeValueExponent_range {σ τ : ℝ}
    (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174)
    (hτ : τ ∈ Set.Icc (2*((30*σ-11)/8)/3) ((30*σ-11)/8)) :
    largeValueExponent σ τ ≤ (((3-3*σ)*τ/((30*σ-11)/8):ℝ):EReal) := by
  let τ₀ := (30*σ-11)/8
  let u := τ/τ₀
  have hτ₀ : 0 < τ₀ := by dsimp only [τ₀]; linarith only [hσ]
  have hu : 2/3 ≤ u := (le_div_iff₀ hτ₀).mpr (by
    dsimp only [τ₀]
    linarith only [hτ.1])
  have hu1 : u ≤ 1 := (div_le_iff₀ hτ₀).mpr (by simpa only [one_mul] using hτ.2)
  have hbound := cdv_largeValueExponent hσ hσhi hu hu1
  have heτ : u*(30*σ-11)/8 = τ := by
    calc
      _ = (τ/τ₀)*τ₀ := by dsimp only [u,τ₀]; ring
      _ = τ := div_mul_cancel₀ _ hτ₀.ne'
  have her : 3*(1-σ)*u = (3-3*σ)*τ/((30*σ-11)/8) := by
    dsimp only [u,τ₀]
    ring
  simpa only [heτ,her] using hbound


private theorem cdv_zeroDensity_lower_range {σ : ℝ}
    (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 155/174) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((24/(30*σ-11):ℝ):EReal) := by
  let τ₀ : ℝ := (30*σ-11)/8
  have hτ₀ : 0 < τ₀ := by dsimp only [τ₀]; linarith only [hσ]
  have hhalf : 1/2 < σ := by linarith only [hσ]
  have hone : σ < 1 := by linarith only [hσhi]
  have hz : ∀ τ ∈ Set.Ico (2:ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/τ₀:ℝ):EReal) := by
    intro τ ht
    apply (zetaLargeValueExponent_le_of_bound
      (ivicNineteenth_zetaLargeValueBound hhalf.le (by linarith only [ht.1])
        (by dsimp only [τ₀] at ht; linarith only [ht.2,hσ]))).trans
    apply EReal.coe_le_coe_iff.mpr
    apply max_le
    · apply (le_div_iff₀ hτ₀).mpr
      have hc : 0 ≤ τ₀-(3-3*σ) := by dsimp only [τ₀]; linarith only [hσ]
      have he : 0 ≤ 1+2*σ-4*τ₀/3 := by dsimp only [τ₀]; linarith only [hσhi]
      have hh := mul_nonneg hc (show 0 ≤ 4*τ₀/3-τ by linarith only [ht.2])
      have hh' := mul_nonneg hτ₀.le he
      nlinarith only [hh,hh']
    · apply (le_div_iff₀ hτ₀).mpr
      have hc : 0 ≤ 3*τ₀-(3-3*σ) := by dsimp only [τ₀]; linarith only [hσ]
      have hh := mul_nonneg hc (show 0 ≤ 4*τ₀/3-τ by linarith only [ht.2])
      dsimp only [τ₀] at hh ⊢
      nlinarith only [hh]
  have hd := zeroDensityExponent_le_three_div_of_largeValue_bounds
    σ τ₀ hhalf hone hτ₀ hz (fun _ ht => cdv_largeValueExponent_range hσ hσhi ht)
  have he : 3/τ₀ = 24/(30*σ-11) := by
    dsimp only [τ₀]
    field_simp
    ring
  simpa only [he] using hd


/-- The CDV lower-range extension together with the proved Ivić upper range.
Both rational endpoints are included; no density output is assumed. -/
theorem zeroDensityExponent_le_cdv_ivic {σ : ℝ}
    (hσ : 279/314 ≤ σ) (hσhi : σ ≤ 17/18) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((24/(30*σ-11):ℝ):EReal) := by
  by_cases hsplit : σ ≤ 155/174
  · exact cdv_zeroDensity_lower_range hσ hsplit
  · exact zeroDensityExponent_le_ivic_nineteenth (le_of_not_ge hsplit) hσhi

end TaoTrudgianYang2025
