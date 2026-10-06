import Dubon2026.TorusPolynomialLog
import Dubon2026.TorusEnergy

/-! # Jensen bounds for the genuine Haar logarithmic potential -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem coeff_zero_finSuccEquiv (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.coeff 0 ((MvPolynomial.finSuccEquiv ℂ n p).coeff 0) = p.coeff 0 := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_zero_zero]

theorem log_coeff_zero_le_integral_log_fin (n : ℕ) (p : MvPolynomial (Fin n) ℂ)
    (hp : p.coeff 0 ≠ 0) :
    Real.log ‖p.coeff 0‖ ≤ ∫ z, Real.log ‖polynomialOnTorus p z‖ ∂circleProductHaar (Fin n) := by
  induction n with
  | zero =>
    have heq : (fun z => Real.log ‖polynomialOnTorus p z‖) =
        (fun _ : UnitAddTorus (Fin 0) => Real.log ‖p.coeff 0‖) := by
      funext z
      change Real.log ‖MvPolynomial.eval _ p‖ = _
      conv_lhs => rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
    rw [heq, integral_const, probReal_univ, one_smul]
  | succ n ih =>
    let q := (MvPolynomial.finSuccEquiv ℂ n p).coeff 0
    have hqcoeff : q.coeff 0 = p.coeff 0 := coeff_zero_finSuccEquiv n p
    have hqc : q.coeff 0 ≠ 0 := hqcoeff ▸ hp
    have hq : q ≠ 0 := by
      intro h
      exact hqc (by rw [h, MvPolynomial.coeff_zero])
    let f : UnitAddTorus (Fin n) × UnitAddCircle → ℝ :=
      fun zu => Real.log ‖polynomialOnTorus p ((finTorusSplit n).symm zu)‖
    have hf : Integrable f
        ((circleProductHaar (Fin n)).prod AddCircle.haarAddCircle) :=
      ((measurePreserving_finTorusSplit n).symm.integrable_comp_emb
        (finTorusSplit n).symm.measurableEmbedding).mpr (integrable_polynomial_log_fin _ p)
    have hbound : (∫ z, Real.log ‖polynomialOnTorus q z‖ ∂circleProductHaar (Fin n)) ≤
        ∫ z, ∫ u, f (z, u) ∂AddCircle.haarAddCircle ∂circleProductHaar (Fin n) := by
      apply integral_mono_ae (integrable_polynomial_log_fin n q) hf.integral_prod_left
      filter_upwards [polynomialOnTorus_ne_zero_ae_fin n q hq] with z hz
      have hc : (polynomialFiber p z).coeff 0 = polynomialOnTorus q z :=
        Polynomial.coeff_map _ _
      have hh := log_coeff_zero_le_integral_log_circle (hc.trans_ne hz)
      simpa only [hc, f, finTorusSplit_symm_apply, polynomialOnTorus_cons] using hh
    rw [← integral_prod f hf] at hbound
    have heq := (measurePreserving_finTorusSplit n).symm.integral_comp'
      (fun z => Real.log ‖polynomialOnTorus p z‖)
    change (∫ zu, f zu ∂(circleProductHaar (Fin n)).prod AddCircle.haarAddCircle) = _ at heq
    rw [heq] at hbound
    exact (hqcoeff ▸ ih q hqc).trans hbound

theorem log_coeff_zero_le_integral_log {ι : Type} [Fintype ι] (p : MvPolynomial ι ℂ)
    (hp : p.coeff 0 ≠ 0) :
    Real.log ‖p.coeff 0‖ ≤ ∫ z, Real.log ‖polynomialOnTorus p z‖ ∂circleProductHaar ι := by
  let e := Fintype.equivFin ι
  have hc : (p.rename e).coeff 0 = p.coeff 0 := MvPolynomial.constantCoeff_rename e p
  have hh := log_coeff_zero_le_integral_log_fin _ (p.rename e) (hc.trans_ne hp)
  have heq := (measurePreserving_torusReindex e).integral_comp'
    (fun z => Real.log ‖polynomialOnTorus (p.rename e) z‖)
  simp only [polynomialOnTorus_rename] at heq
  rwa [hc, ← heq] at hh

/-- The actual normalized Haar log integral; the vertical-mean identity is a separate obligation. -/
def haarLogPotential (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N

theorem haarLogPotential_nonneg {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 = 1)
    (σ : ℝ) : 0 ≤ haarLogPotential a N σ := by
  have hc : (bohrPolynomial a N σ).coeff 0 ≠ 0 := by
    rw [coeff_zero_bohrPolynomial a hN σ, ha]
    exact one_ne_zero
  have h := log_coeff_zero_le_integral_log (bohrPolynomial a N σ) hc
  simpa only [coeff_zero_bohrPolynomial a hN σ, ha, norm_one, Real.log_one,
    polynomialOnTorus_bohrPolynomial, circleProductHaar, torusHaar, haarLogPotential] using h


theorem haarLogPotential_le_half_log_energy {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (ha : a 1 = 1) (σ : ℝ) :
    haarLogPotential a N σ ≤ Real.log (coefficientEnergy a N σ) / 2 := by
  let E := coefficientEnergy a N σ
  have hE : 0 < E := lt_of_lt_of_le zero_lt_one (one_le_coefficientEnergy hN ha σ)
  have ha0 : a 1 ≠ 0 := ha.trans_ne one_ne_zero
  have hlog := integrable_bohrOnTorus_log a N σ
  have hsq : Integrable (fun z => ‖bohrOnTorus a N σ z‖ ^ 2) (torusHaar N) :=
    ((bohrOnTorus a N σ).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ᵐ z ∂torusHaar N,
      2 * Real.log ‖bohrOnTorus a N σ z‖ - Real.log E ≤
        ‖bohrOnTorus a N σ z‖ ^ 2 / E - 1 := by
    filter_upwards [bohrOnTorus_ne_zero_ae hN ha0 σ] with z hz
    have hpos : 0 < ‖bohrOnTorus a N σ z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have hh := Real.log_le_sub_one_of_pos (div_pos hpos hE)
    rwa [Real.log_div hpos.ne' hE.ne', Real.log_pow, Nat.cast_ofNat] at hh
  have hh := integral_mono_ae ((hlog.const_mul 2).sub (integrable_const (Real.log E)))
    ((hsq.div_const E).sub (integrable_const 1)) hbound
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hlog.const_mul 2) (integrable_const (Real.log E)),
    integral_sub (hsq.div_const E) (integrable_const 1)] at hh
  simp only [integral_const_mul, integral_div, integral_const,
    probReal_univ, one_smul, integral_norm_sq_bohrOnTorus] at hh
  change 2 * haarLogPotential a N σ - Real.log E ≤ E / E - 1 at hh
  rw [div_self hE.ne'] at hh
  dsimp only [E] at hh
  linarith

theorem haarLogPotential_bounds {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 = 1)
    (σ : ℝ) : 0 ≤ haarLogPotential a N σ ∧
      haarLogPotential a N σ ≤ Real.log (coefficientEnergy a N σ) / 2 :=
  ⟨haarLogPotential_nonneg hN ha σ, haarLogPotential_le_half_log_energy hN ha σ⟩

end

end Dubon2026
