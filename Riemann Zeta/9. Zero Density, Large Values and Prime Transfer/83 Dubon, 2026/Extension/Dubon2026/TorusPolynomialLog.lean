import Dubon2026.CirclePolynomialLog
import Dubon2026.MultivariateBohrPolynomial
import Mathlib.MeasureTheory.Integral.Pi

/-! # Logarithms of polynomials on finite products of circles -/

namespace Dubon2026

open MeasureTheory MeasureTheory.Measure

noncomputable section

/-- Normalized product Haar measure for an arbitrary finite set of circle coordinates. -/
def circleProductHaar (ι : Type) [Fintype ι] : Measure (UnitAddTorus ι) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle)

instance circleProductHaarProbability (ι : Type) [Fintype ι] :
    IsProbabilityMeasure (circleProductHaar ι) := by
  unfold circleProductHaar
  infer_instance

/-- Separate the first circle coordinate, with the remaining coordinates first. -/
def finTorusSplit (n : ℕ) :
    UnitAddTorus (Fin (n + 1)) ≃ᵐ UnitAddTorus (Fin n) × UnitAddCircle :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0).trans
    MeasurableEquiv.prodComm

theorem finTorusSplit_symm_apply (n : ℕ) (z : UnitAddTorus (Fin n)) (u : UnitAddCircle) :
    (finTorusSplit n).symm (z, u) = Fin.cons u z := by
  simp [finTorusSplit, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]
  exact ⟨rfl, rfl⟩

theorem measurePreserving_finTorusSplit (n : ℕ) :
    MeasurePreserving (finTorusSplit n) (circleProductHaar (Fin (n + 1)))
      ((circleProductHaar (Fin n)).prod AddCircle.haarAddCircle) := by
  exact measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => AddCircle.haarAddCircle) 0)

/-- Regard the first variable as a one-variable polynomial after evaluating all others. -/
def polynomialFiber {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℂ)
    (z : UnitAddTorus (Fin n)) : Polynomial ℂ :=
  (MvPolynomial.finSuccEquiv ℂ n p).map (MvPolynomial.eval (fun i => fourier 1 (z i)))

theorem polynomialOnTorus_cons {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℂ)
    (z : UnitAddTorus (Fin n)) (u : UnitAddCircle) :
    polynomialOnTorus p (Fin.cons u z) = (polynomialFiber p z).eval (fourier 1 u) := by
  simp only [polynomialOnTorus, ContinuousMap.coe_mk]
  unfold polynomialFiber
  have h : (fun i : Fin (n + 1) => fourier 1 ((Fin.cons u z : Fin (n + 1) → UnitAddCircle) i)) =
      Fin.cons (fourier 1 u) (fun i => fourier 1 (z i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [h, MvPolynomial.eval_eq_eval_mv_eval']

theorem polynomialFiber_leadingCoeff {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℂ)
    (z : UnitAddTorus (Fin n))
    (hz : polynomialOnTorus (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff z ≠ 0) :
    (polynomialFiber p z).leadingCoeff =
      polynomialOnTorus (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff z := by
  exact Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz

theorem polynomialFiber_ne_zero {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℂ)
    (z : UnitAddTorus (Fin n))
    (hz : polynomialOnTorus (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff z ≠ 0) :
    polynomialFiber p z ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rwa [polynomialFiber_leadingCoeff p z hz]

theorem polynomialOnTorus_ne_zero_ae_fin (n : ℕ) (p : MvPolynomial (Fin n) ℂ)
    (hp : p ≠ 0) :
    ∀ᵐ z ∂circleProductHaar (Fin n), polynomialOnTorus p z ≠ 0 := by
  induction n with
  | zero =>
    have hcoeff : p.coeff 0 ≠ 0 := by
      intro h
      exact hp (by rw [MvPolynomial.eq_C_of_isEmpty p, h, map_zero])
    apply Filter.Eventually.of_forall
    intro z
    change MvPolynomial.eval _ p ≠ 0
    rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
    exact hcoeff
  | succ n ih =>
    have hlead : (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (by
        intro h
        apply hp
        apply (MvPolynomial.finSuccEquiv ℂ n).injective
        simpa only [map_zero] using h)
    have htail := ih _ hlead
    have hprod : ∀ᵐ zu ∂(circleProductHaar (Fin n)).prod AddCircle.haarAddCircle,
        polynomialOnTorus p ((finTorusSplit n).symm zu) ≠ 0 := by
      apply (ae_prod_iff_ae_ae (by
        exact (isClosed_singleton.preimage ((polynomialOnTorus p).continuous)).measurableSet.compl.preimage
          (finTorusSplit n).symm.measurable)).mpr
      filter_upwards [htail] with z hz
      simpa only [finTorusSplit_symm_apply, polynomialOnTorus_cons] using
        polynomial_ne_zero_ae_circle (polynomialFiber_ne_zero p z hz)
    have h := (measurePreserving_finTorusSplit n).quasiMeasurePreserving.ae hprod
    simpa only [MeasurableEquiv.symm_apply_apply] using h


theorem measurable_polynomial_log {ι : Type} [Fintype ι] (p : MvPolynomial ι ℂ) :
    Measurable (fun z => Real.log ‖polynomialOnTorus p z‖) :=
  Real.measurable_log.comp (polynomialOnTorus p).continuous.norm.measurable

theorem integrable_polynomial_log_fin (n : ℕ) (p : MvPolynomial (Fin n) ℂ) :
    Integrable (fun z => Real.log ‖polynomialOnTorus p z‖) (circleProductHaar (Fin n)) := by
  induction n with
  | zero =>
    have heq : (fun z => Real.log ‖polynomialOnTorus p z‖) =
        (fun _ : UnitAddTorus (Fin 0) => Real.log ‖p.coeff 0‖) := by
      funext z
      change Real.log ‖MvPolynomial.eval _ p‖ = _
      conv_lhs => rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
    rw [heq]
    exact integrable_const _
  | succ n ih =>
    by_cases hp : p = 0
    · subst p
      simpa only [polynomialOnTorus, ContinuousMap.coe_mk, map_zero, norm_zero,
        Real.log_zero] using (integrable_const (0 : ℝ) :
          Integrable (fun _ : UnitAddTorus (Fin (n + 1)) => (0 : ℝ)) _)
    let q := (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff
    have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (by
      intro h
      apply hp
      apply (MvPolynomial.finSuccEquiv ℂ n).injective
      simpa only [map_zero] using h)
    let f : UnitAddTorus (Fin n) × UnitAddCircle → ℝ :=
      fun zu => Real.log ‖polynomialOnTorus p ((finTorusSplit n).symm zu)‖
    have hm : Measurable f :=
      (measurable_polynomial_log p).comp (finTorusSplit n).symm.measurable
    let C : ℝ := ‖polynomialOnTorus p‖
    have hC : 0 ≤ C := norm_nonneg _
    have hbound (z : UnitAddTorus (Fin n)) (u : UnitAddCircle) :
        Real.log ‖(polynomialFiber p z).eval (fourier 1 u)‖ ≤ C := by
      rw [← polynomialOnTorus_cons]
      exact (Real.log_le_self (norm_nonneg _)).trans
        ((polynomialOnTorus p).norm_coe_le_norm _)
    have hinner (z : UnitAddTorus (Fin n)) : Integrable (fun u => f (z, u))
        AddCircle.haarAddCircle := by
      simpa only [f, finTorusSplit_symm_apply, polynomialOnTorus_cons] using
        integrable_polynomial_log_circle (polynomialFiber p z)
    have hnorm : Integrable
        (fun z => ∫ u, ‖f (z, u)‖ ∂AddCircle.haarAddCircle) (circleProductHaar (Fin n)) := by
      apply ((integrable_const (2 * C)).add (ih q).abs).mono'
        hm.aestronglyMeasurable.norm.integral_prod_right'
      filter_upwards [polynomialOnTorus_ne_zero_ae_fin n q hq] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have hb := integral_abs_log_circle_le (polynomialFiber p z) hC (hbound z)
      rw [polynomialFiber_leadingCoeff p z hz] at hb
      simp only [f, finTorusSplit_symm_apply, polynomialOnTorus_cons, Real.norm_eq_abs]
      exact hb.trans (by dsimp only [Pi.add_apply]; linarith [neg_le_abs (Real.log ‖polynomialOnTorus q z‖)])
    have hprod : Integrable f
        ((circleProductHaar (Fin n)).prod AddCircle.haarAddCircle) :=
      (integrable_prod_iff hm.aestronglyMeasurable).mpr
        ⟨Filter.Eventually.of_forall hinner, hnorm⟩
    exact ((measurePreserving_finTorusSplit n).symm.integrable_comp_emb
      (finTorusSplit n).symm.measurableEmbedding).mp hprod


/-- Relabel circle coordinates by an equivalence. -/
def torusReindex {ι κ : Type} (e : ι ≃ κ) : UnitAddTorus ι ≃ᵐ UnitAddTorus κ :=
  MeasurableEquiv.piCongrLeft (fun _ : κ => UnitAddCircle) e

theorem measurePreserving_torusReindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (torusReindex e) (circleProductHaar ι) (circleProductHaar κ) :=
  measurePreserving_piCongrLeft (fun _ : κ => AddCircle.haarAddCircle) e

theorem polynomialOnTorus_rename {ι κ : Type} (e : ι ≃ κ) (p : MvPolynomial ι ℂ)
    (z : UnitAddTorus ι) :
    polynomialOnTorus (p.rename e) (torusReindex e z) = polynomialOnTorus p z := by
  simp only [polynomialOnTorus, ContinuousMap.coe_mk, MvPolynomial.eval_rename]
  simp only [Function.comp_def, torusReindex, MeasurableEquiv.piCongrLeft_apply_apply]

theorem polynomialOnTorus_ne_zero_ae {ι : Type} [Fintype ι] (p : MvPolynomial ι ℂ)
    (hp : p ≠ 0) : ∀ᵐ z ∂circleProductHaar ι, polynomialOnTorus p z ≠ 0 := by
  let e := Fintype.equivFin ι
  have hq : p.rename e ≠ 0 := by
    intro h
    apply hp
    apply MvPolynomial.rename_injective e e.injective
    simpa only [map_zero] using h
  have hfin := polynomialOnTorus_ne_zero_ae_fin _ (p.rename e) hq
  have h := (measurePreserving_torusReindex e).quasiMeasurePreserving.ae hfin
  simpa only [polynomialOnTorus_rename] using h

theorem integrable_polynomial_log {ι : Type} [Fintype ι] (p : MvPolynomial ι ℂ) :
    Integrable (fun z => Real.log ‖polynomialOnTorus p z‖) (circleProductHaar ι) := by
  let e := Fintype.equivFin ι
  have hfin := integrable_polynomial_log_fin _ (p.rename e)
  have h := ((measurePreserving_torusReindex e).integrable_comp_emb
    (torusReindex e).measurableEmbedding).mpr hfin
  change Integrable (fun z => Real.log ‖polynomialOnTorus (p.rename e) (torusReindex e z)‖) _ at h
  simpa only [polynomialOnTorus_rename] using h

theorem bohrOnTorus_ne_zero_ae {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (σ : ℝ) : ∀ᵐ z ∂torusHaar N, bohrOnTorus a N σ z ≠ 0 := by
  simpa only [polynomialOnTorus_bohrPolynomial, circleProductHaar, torusHaar] using
    polynomialOnTorus_ne_zero_ae (bohrPolynomial a N σ) (bohrPolynomial_ne_zero hN ha σ)

theorem integrable_bohrOnTorus_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Integrable (fun z => Real.log ‖bohrOnTorus a N σ z‖) (torusHaar N) := by
  simpa only [polynomialOnTorus_bohrPolynomial, circleProductHaar, torusHaar] using
    integrable_polynomial_log (bohrPolynomial a N σ)

end

end Dubon2026
