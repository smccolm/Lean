import TaoTrudgianYang2025.IvicSixthSmoothGram
import TaoTrudgianYang2025.BourgainMellinLocalization

/-! The fixed smooth Gram trace has a genuine localized critical-line entry. -/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

def ivicSixthTraceProfile (x : ℝ) : ℂ := (zetaIntervalCutoff 1 2 x:ℂ)^2

def ivicSixthTraceProfileTest : DFIVoronoiTestFunction ivicSixthTraceProfile where
  lower := 1/2
  upper := 5/2
  lower_pos := by norm_num
  lower_le_upper := by norm_num
  smooth := (Complex.ofRealCLM.contDiff.comp (contDiff_zetaIntervalCutoff 1 2)).pow 2
  support_subset := by
    intro x hx
    have hn : zetaIntervalCutoff 1 2 x ≠ 0 := by
      intro hz
      exact hx (by simp [ivicSixthTraceProfile,hz])
    convert support_zetaIntervalCutoff 1 2 hn using 1
    norm_num

theorem ivicSixthTraceProfile_zero : ivicSixthTraceProfile 0 = 0 := by
  have hz : zetaIntervalCutoff 1 2 0 = 0 :=
    zetaIntervalCutoff_eq_zero_left (by norm_num)
  simp only [ivicSixthTraceProfile,hz,ofReal_zero,zero_pow (by norm_num : 2 ≠ 0)]

theorem bourgainCriticalWeight_half_normalization (g : ℝ → ℂ)
    {L x : ℝ} (hL : 0 < L) (hx : 0 < x) :
    ((L^(1/2:ℝ):ℝ):ℂ)*
      bourgainCriticalWeight (bourgainRealPowerWeight (1/2) g) L x = g (x/L) := by
  unfold bourgainCriticalWeight bourgainRealPowerWeight
  dsimp only
  rw [Real.div_rpow hx.le hL.le,
    show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg hx.le]
  push_cast
  have hLc : ((L^(1/2:ℝ):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hL _).ne'
  have hxc : ((x^(1/2:ℝ):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
  field_simp [hLc,hxc]

theorem ivicSixthSmoothTrace_critical_normalization {Q : ℕ} (hQ : 0 < Q) (t : ℝ) :
    ivicSixthSmoothTrace Q t =
      ((Real.sqrt (Q:ℝ):ℝ):ℂ)*
        ∑' n : ℕ, bourgainCriticalWeight
          (bourgainRealPowerWeight (1/2) ivicSixthTraceProfile) Q n*dirichletPhase n t := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  rw [ivicSixthSmoothTrace_eq_tsum hQ,Real.sqrt_eq_rpow,← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    have hz : zetaIntervalCutoff 1 2 0 = 0 :=
      zetaIntervalCutoff_eq_zero_left (by norm_num)
    simp [bourgainCriticalWeight,bourgainRealPowerWeight,ivicSixthTraceProfile,hz]
  · have hn0 : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    rw [← mul_assoc,
      bourgainCriticalWeight_half_normalization ivicSixthTraceProfile hQ0 hn0]
    rfl

theorem ivicSixthSmoothTrace_localized (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q → ∀ t H : ℝ, 0 ≤ H →
      ‖ivicSixthSmoothTrace Q t‖ ≤ C*
        ((Q:ℝ)/(1+|t|)^q+
          Real.sqrt (Q:ℝ)*(∫ u in -H..H,zetaMomentCriticalNorm (u+t))+
          Real.sqrt (Q:ℝ)*(1+|t|)/(1+H)^q) := by
  obtain ⟨C,hC,hbound⟩ := bourgainCriticalWeight_localized
    (bourgainRealPowerWeightTest ivicSixthTraceProfileTest (1/2)) q
  refine ⟨C,hC,?_⟩
  intro Q hQ t H hH
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  rw [ivicSixthSmoothTrace_critical_normalization hQ,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply le_trans (mul_le_mul_of_nonneg_left (hbound Q hQ0 t H hH) (Real.sqrt_nonneg _))
  have he : Real.sqrt (Q:ℝ)*(C*(Real.sqrt (Q:ℝ)/(1+|t|)^q+
      (∫ u in -H..H,zetaMomentCriticalNorm (u+t))+(1+|t|)/(1+H)^q)) =
      C*((Q:ℝ)/(1+|t|)^q+
        Real.sqrt (Q:ℝ)*(∫ u in -H..H,zetaMomentCriticalNorm (u+t))+
        Real.sqrt (Q:ℝ)*(1+|t|)/(1+H)^q) := by
    calc
      _ = C*(Real.sqrt (Q:ℝ)^2/(1+|t|)^q+
        Real.sqrt (Q:ℝ)*(∫ u in -H..H,zetaMomentCriticalNorm (u+t))+
        Real.sqrt (Q:ℝ)*(1+|t|)/(1+H)^q) := by ring
      _ = _ := by rw [Real.sq_sqrt hQ0.le]
  exact he.le

end TaoTrudgianYang2025
