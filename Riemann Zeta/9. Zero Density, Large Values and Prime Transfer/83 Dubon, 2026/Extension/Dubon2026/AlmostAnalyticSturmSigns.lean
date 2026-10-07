import Dubon2026.AlmostAnalyticRootLayers

/-! # Generic local constancy of the signs in the actual Euclidean Sturm chain -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- Signs of the actual polynomial evaluations along a Sturm chain. -/
def chainSignList (chain : List ℝ[X]) (t : ℝ) : List SignType :=
  chain.map (fun P => SignType.sign (P.eval t))

theorem sturmVar_eq_of_chainSignList_eq {A B : List ℝ[X]} {t : ℝ}
    (h : chainSignList A t = chainSignList B t) : Sturm.sturmVar A t = Sturm.sturmVar B t := by
  apply Sturm.signVariations_congr
  have he : List.Forall₂ (fun a b : SignType => a = b)
      ((A.map (Polynomial.eval t)).map SignType.sign)
      ((B.map (Polynomial.eval t)).map SignType.sign) := by
    rw [List.forall₂_eq_eq_eq]
    simpa only [List.map_map, Function.comp_def, chainSignList] using h
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using he

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem ae_signedRemainderTail_signs_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (n : ℕ) {P Q : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hdP : ∀ y, (P y).natDegree ≤ d) (hdQ : ∀ y, (Q y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y)
    (hQ : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (Q z).coeff k) y) (t : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      chainSignList (signedRemainderTail (P z) (Q z) n) t =
        chainSignList (signedRemainderTail (P y) (Q y) n) t := by
  induction n generalizing P Q with
  | zero => exact Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
  | succ n ih =>
    let R : V → ℝ[X] := fun y => -(P y % Q y)
    have hR : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (R z).coeff k) y := by
      intro k
      filter_upwards [ae_polynomial_mod_coeff_analytic μ hdP hdQ hP hQ k] with y hy
      simpa only [R, Polynomial.coeff_neg] using hy.neg
    have hdR : ∀ y, (R y).natDegree ≤ d := by
      intro y
      simpa only [R, Polynomial.natDegree_neg] using
        (polynomial_natDegree_mod_le_left (P y) (Q y)).trans (hdP y)
    have hr := ih hdQ hdR hQ hR
    have hsign := ae_analytic_sign_locally_constant μ (ae_polynomial_eval_analytic μ hdR hR t)
    filter_upwards [hr, hsign, ae_polynomial_natDegree_locally_constant μ hdQ hQ]
      with y hry hsy hdy
    filter_upwards [hry, hsy, hdy] with z hrz hsz hdz
    simp only [signedRemainderTail, hdz]
    split_ifs
    · rfl
    · change SignType.sign ((R z).eval t) :: chainSignList (signedRemainderTail (Q z) (R z) n) t =
        SignType.sign ((R y).eval t) :: chainSignList (signedRemainderTail (Q y) (R y) n) t
      rw [hsz, hrz]

theorem ae_euclideanSturmChain_signs_locally_constant (μ : Measure V)
    [Measure.IsAddHaarMeasure μ] {P : V → ℝ[X]} {s : Set V} {d : ℕ}
    (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (t : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      chainSignList (euclideanSturmChain (P z)) t = chainSignList (euclideanSturmChain (P y)) t := by
  have hD := ae_polynomial_derivative_coeff_analytic μ hP
  have hdD : ∀ y, (P y).derivative.natDegree ≤ d := fun y =>
    ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans (hdP y)
  have htails : ∀ᵐ y ∂μ.restrict s, ∀ n, ∀ᶠ z in 𝓝 y,
      chainSignList (signedRemainderTail (P z) (P z).derivative n) t =
        chainSignList (signedRemainderTail (P y) (P y).derivative n) t :=
    ae_all_iff.mpr (fun n => ae_signedRemainderTail_signs_locally_constant μ n hdP hdD hP hD t)
  filter_upwards [htails, ae_polynomial_natDegree_locally_constant μ hdD hD,
    ae_analytic_sign_locally_constant μ (ae_polynomial_eval_analytic μ hdP hP t),
    ae_analytic_sign_locally_constant μ (ae_polynomial_eval_analytic μ hdD hD t)]
    with y hty hdy hpy hqy
  filter_upwards [hty ((P y).derivative.natDegree + 1), hdy, hpy, hqy]
    with z htz hdz hpz hqz
  simp only [euclideanSturmChain, chainSignList, List.map_cons, hdz]
  change _ :: _ :: chainSignList (signedRemainderTail (P z) (P z).derivative
      ((P y).derivative.natDegree + 1)) t = _ :: _ :: _
  rw [hpz, hqz, htz]
  rfl

theorem ae_sturmVar_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {P : V → ℝ[X]} {s : Set V} {d : ℕ} (hdP : ∀ y, (P y).natDegree ≤ d)
    (hP : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (P z).coeff k) y) (t : ℝ) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y,
      Sturm.sturmVar (euclideanSturmChain (P z)) t =
        Sturm.sturmVar (euclideanSturmChain (P y)) t := by
  filter_upwards [ae_euclideanSturmChain_signs_locally_constant μ hdP hP t] with y hy
  exact hy.mono (fun _ hz => sturmVar_eq_of_chainSignList_eq hz)

end

end Dubon2026
