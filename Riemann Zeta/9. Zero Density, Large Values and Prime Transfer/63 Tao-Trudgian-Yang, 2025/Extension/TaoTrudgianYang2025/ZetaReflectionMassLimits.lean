import TaoTrudgianYang2025.ZetaReflectionAmplitudeLimits
import TaoTrudgianYang2025.ZetaLargeValueSequentialBounds

/-! The retained actual amplitude-cardinality mass gives a limiting affine comparison. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

theorem reflection_mass_log_comparison (P Q : ℕ → ZetaLargeValuePattern)
    (err : ℕ → ℝ) {r a v κ σ' τ' b : ℝ} (hκ : 0 < κ)
    (hQtop : Tendsto (fun n => (Q n).N) atTop atTop)
    (hQT : Tendsto (fun n => Real.logb (Q n).N (Q n).T) atTop (nhds τ'))
    (hQV : Tendsto (fun n => Real.logb (Q n).N (Q n).V) atTop (nhds σ'))
    (hne : ∀ n, (Q n).ordinates.Nonempty)
    (hscale : Tendsto (fun n => Real.logb (P n).N (Q n).N) atTop (nhds κ))
    (hvalue : Tendsto (fun n => Real.logb (P n).N (Q n).V) atTop (nhds v))
    (hfloor : Tendsto (fun n => Real.logb (P n).N
      ((P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n))))
      atTop (nhds a))
    (hcard : ∀ n, (P n).N^r ≤ ((P n).ordinates.card : ℝ))
    (hmass : ∀ n, ((P n).ordinates.card : ℝ)*(P n).V*Real.sqrt (P n).T/
      ((P n).N*(P n).N^(err n)) ≤ (Q n).V*((Q n).ordinates.card : ℝ))
    (hbound : IsZetaLargeValueBound σ' τ' b) :
    r+a ≤ v+κ*b := by
  have happrox (e : ℝ) (he : 0 < e) : r+a ≤ v+κ*(b+e) := by
    have hseq := hbound.eventually_log_card_le Q hQtop hQT hQV hne he
    have hlower : Tendsto (fun n => r+Real.logb (P n).N
        ((P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n))))
        atTop (nhds (r+a)) := tendsto_const_nhds.add hfloor
    have hupper : Tendsto (fun n => Real.logb (P n).N (Q n).V+
        Real.logb (P n).N (Q n).N*(b+e)) atTop (nhds (v+κ*(b+e))) :=
      hvalue.add (hscale.mul_const (b+e))
    apply le_of_tendsto_of_tendsto hlower hupper
    filter_upwards [hseq] with n hn
    let F := (P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n))
    have hN := zero_lt_one.trans (P n).one_lt_N
    have hF : 0 < F := div_pos
      (mul_pos (P n).V_pos (Real.sqrt_pos.mpr (P n).T_pos))
      (mul_pos hN (Real.rpow_pos_of_pos hN _))
    have hQcard : (0 : ℝ) < (Q n).ordinates.card := by exact_mod_cast (hne n).card_pos
    have hpow := Real.rpow_pos_of_pos hN r
    have hfinite : (P n).N^r*F ≤ (Q n).V*((Q n).ordinates.card : ℝ) := by
      have h := mul_le_mul_of_nonneg_right (hcard n) hF.le
      have hm : ((P n).ordinates.card : ℝ)*F ≤ (Q n).V*((Q n).ordinates.card : ℝ) := by
        convert hmass n using 1
        dsimp [F]
        ring
      exact h.trans hm
    have hl := (Real.logb_le_logb (P n).one_lt_N (mul_pos hpow hF)
      (mul_pos (Q n).V_pos hQcard)).mpr hfinite
    have hp : Real.logb (P n).N ((P n).N^r) = r := by
      rw [Real.logb,Real.log_rpow hN]
      field_simp [(Real.log_pos (P n).one_lt_N).ne']
    rw [Real.logb_mul hpow.ne' hF.ne',hp,
      Real.logb_mul (Q n).V_pos.ne' hQcard.ne'] at hl
    have hchange : Real.logb (P n).N ((Q n).ordinates.card : ℝ) =
        Real.logb (P n).N (Q n).N*Real.logb (Q n).N ((Q n).ordinates.card : ℝ) := by
      unfold Real.logb
      field_simp [(Real.log_pos (P n).one_lt_N).ne',(Real.log_pos (Q n).one_lt_N).ne']
    have hs : 0 ≤ Real.logb (P n).N (Q n).N :=
      div_nonneg (Real.log_pos (Q n).one_lt_N).le (Real.log_pos (P n).one_lt_N).le
    have hu := mul_le_mul_of_nonneg_left hn hs
    rw [← hchange] at hu
    change r+Real.logb (P n).N F ≤ _
    linarith
  by_contra hnot
  have hgap : 0 < r+a-(v+κ*b) := sub_pos.mpr (lt_of_not_ge hnot)
  let e := (r+a-(v+κ*b))/(2*κ)
  have he : 0 < e := div_pos hgap (by positivity)
  have heq : κ*e = (r+a-(v+κ*b))/2 := by dsimp [e]; field_simp
  have h := happrox e he
  nlinarith

theorem reflection_mass_le_zeta_exponent (P Q : ℕ → ZetaLargeValuePattern)
    (err : ℕ → ℝ) {r a v κ σ' τ' : ℝ} (hκ : 0 < κ)
    (hQtop : Tendsto (fun n => (Q n).N) atTop atTop)
    (hQT : Tendsto (fun n => Real.logb (Q n).N (Q n).T) atTop (nhds τ'))
    (hQV : Tendsto (fun n => Real.logb (Q n).N (Q n).V) atTop (nhds σ'))
    (hne : ∀ n, (Q n).ordinates.Nonempty)
    (hscale : Tendsto (fun n => Real.logb (P n).N (Q n).N) atTop (nhds κ))
    (hvalue : Tendsto (fun n => Real.logb (P n).N (Q n).V) atTop (nhds v))
    (hfloor : Tendsto (fun n => Real.logb (P n).N
      ((P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n))))
      atTop (nhds a))
    (hcard : ∀ n, (P n).N^r ≤ ((P n).ordinates.card : ℝ))
    (hmass : ∀ n, ((P n).ordinates.card : ℝ)*(P n).V*Real.sqrt (P n).T/
      ((P n).N*(P n).N^(err n)) ≤ (Q n).V*((Q n).ordinates.card : ℝ)) :
    (((r+a-v)/κ : ℝ) : EReal) ≤ zetaLargeValueExponent σ' τ' := by
  apply le_sInf
  rintro _ ⟨b,hb,rfl⟩
  change (((r+a-v)/κ : ℝ) : EReal) ≤ (b : EReal)
  apply EReal.coe_le_coe_iff.mpr
  apply (div_le_iff₀ hκ).mpr
  have h := reflection_mass_log_comparison P Q err hκ hQtop hQT hQV hne
    hscale hvalue hfloor hcard hmass hb
  linarith

end TaoTrudgianYang2025
