
import TaoTrudgianYang2025.IvicNineteenthDensity
import TaoTrudgianYang2025.BourgainZetaBands

noncomputable section
open MeasureTheory Filter Set
open scoped Interval
namespace IvicMixedBandScratch
open TaoTrudgianYang2025

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

example : ∀ {T V : ℝ}, 0 ≤ T → 0 ≤ V →
    (V/2)^6*volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T, ivicSixthExcess (V/2) t^6 := @band_excess_mass
example : ∀ {ε : ℝ}, 0 < ε →
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T V : ℝ, B ≤ T → 0 < V →
      volume.real (bourgainZetaBand T V) ≤ C*T^ε*(T/V^6+T^3/V^19) :=
  @band_two_term_tail
#print axioms band_excess_mass
#print axioms band_two_term_tail

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

example : ∀ {ε : ℝ}, 0 < ε →
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T V : ℝ, B ≤ T → 0 < V →
      (V ≤ T^(2/13:ℝ) →
        V^19*volume.real (bourgainZetaBand T V) ≤ C*T^(3+ε)) ∧
      (T^(2/13:ℝ) ≤ V →
        V^6*volume.real (bourgainZetaBand T V) ≤ C*T^(1+ε)) := @mixed_band_bounds
#print axioms mixed_band_bounds

end IvicMixedBandScratch
