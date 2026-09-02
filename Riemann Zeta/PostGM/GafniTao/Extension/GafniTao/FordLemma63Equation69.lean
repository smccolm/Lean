import GafniTao.FordLemma63WeightedOverlap

/-!
# Ford Lemma 6.3: equation (6.9)

The torus boxes are lifted coordinatewise to the literal real phase boxes,
so the Abel majorant proved earlier applies without changing representatives.
-/

open Complex Finset Set MeasureTheory Metric
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem continuous_fordLemma63SZeroTorus (k M : ℕ) :
    Continuous (fordLemma63SZeroTorus k M) := by
  have hweyl (Q : ℕ) : Continuous (fordVinogradovWeylSum k Q) := by
    unfold fordVinogradovWeylSum fordVinogradovMonomial
    fun_prop
  unfold fordLemma63SZeroTorus
  fun_prop

theorem integrable_fordLemma63SZeroTorus_pow (s k M : ℕ) :
    Integrable (fun α : UnitAddTorus (Fin k) =>
      fordLemma63SZeroTorus k M α ^ (2 * s))
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
  rw [← integrableOn_univ]
  exact ((continuous_fordLemma63SZeroTorus k M).pow (2 * s)).continuousOn
    |>.integrableOn_compact isCompact_univ

theorem exists_real_lift_mem_closedBall
    {a : UnitAddCircle} {γ r : ℝ}
    (ha : a ∈ closedBall (γ : UnitAddCircle) r) :
    ∃ β : ℝ, (β : UnitAddCircle) = a ∧ |β - γ| ≤ r := by
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hxcoe : (x : UnitAddCircle) = a := by
    dsimp [x]
    change (AddCircle.equivIoc 1 0).symm
      ((AddCircle.equivIoc 1 0) a) = a
    exact (AddCircle.equivIoc 1 0).symm_apply_apply a
  have hpre : x ∈ ((fun y : ℝ => (y : UnitAddCircle)) ⁻¹'
      (closedBall (γ : UnitAddCircle) r : Set UnitAddCircle)) := by
    show (x : UnitAddCircle) ∈ closedBall (γ : UnitAddCircle) r
    rw [hxcoe]
    exact ha
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hpre
  simp only [Set.mem_iUnion] at hpre
  obtain ⟨z, hz⟩ := hpre
  refine ⟨x - (z : ℝ), ?_, ?_⟩
  · calc
      ((x - (z : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        have hzmem : (-(z : ℝ)) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
          rw [← Int.cast_neg]
          exact AddSubgroup.intCast_mem_zmultiples_one (-z)
        convert hzmem using 1
        ring
      _ = a := hxcoe
  · have hdist : |x - (γ + (z : ℝ))| ≤ r := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one]
        using hz
    have heq : |x - (z : ℝ) - γ| = |x - (γ + (z : ℝ))| := by
      congr 1
      ring
    rw [heq]
    exact hdist

theorem exists_real_lift_mem_fordLemma63Omega
    {k M n : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)}
    (hα : α ∈ fordLemma63TorusOmega k M n u t) :
    ∃ β : Fin k → ℝ,
      β ∈ fordLemma63Omega k M n u t ∧
      (∀ j, (β j : UnitAddCircle) = α j) := by
  classical
  have hj (j : Fin k) : ∃ β : ℝ,
      (β : UnitAddCircle) = α j ∧
      |β - fordTaylorGamma t ((n : ℝ) + u) j| ≤
        fordLemma63Radius k M j :=
    exists_real_lift_mem_closedBall
      ((fordLemma63TorusOmega_mem.mp hα) j)
  choose β hβcoe hβbound using hj
  exact ⟨β, hβbound, hβcoe⟩

theorem norm_fordLemma63T_le_SZeroTorus_on_box
    {k M N n : ℕ} {u t : ℝ} {α : UnitAddTorus (Fin k)}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hα : α ∈ fordLemma63TorusOmega k M n u t) :
    ‖fordLemma63T M n u t‖ ≤ fordLemma63SZeroTorus k M α := by
  obtain ⟨β, hβOmega, hβcoe⟩ :=
    exists_real_lift_mem_fordLemma63Omega hα
  calc
    ‖fordLemma63T M n u t‖ ≤ fordLemma63SZero k M β :=
      norm_fordLemma63T_le_SZero hk hM hN hn hu ht hscale hβOmega
    _ = fordLemma63SZeroTorus k M α := by
      rw [fordLemma63SZero_eq_torus]
      congr 1
      funext j
      exact hβcoe j

/-- Ford's equation (6.9), with the exact phase-volume denominator, overlap
constant, and Vinogradov moment retained. -/
theorem ford_equation_6_9
    {s k M N : ℕ} {u t : ℝ}
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      ‖fordLemma63T M n u t‖ ^ (2 * s)) ≤
      (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k) *
      fordLemma63W N k M t *
      ((2 : ℝ) ^ (4 * s) *
        (fordVinogradovMomentNat s k M : ℝ)) := by
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  let D : ℝ := Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
    (M : ℝ) ^ fordVinogradovKappa k
  let F : UnitAddTorus (Fin k) → ℝ := fun α =>
    fordLemma63SZeroTorus k M α ^ (2 * s)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hFnonneg (α : UnitAddTorus (Fin k)) : 0 ≤ F α := by
    dsimp [F]
    apply pow_nonneg
    unfold fordLemma63SZeroTorus
    positivity
  have hFint : Integrable F μ := by
    exact integrable_fordLemma63SZeroTorus_pow s k M
  have hsingle (n : ℕ) (hn : n ∈ Finset.Ioc N (2 * N - 1)) :
      ‖fordLemma63T M n u t‖ ^ (2 * s) ≤
        D * ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ := by
    let A : ℝ := ‖fordLemma63T M n u t‖ ^ (2 * s)
    have hpoint (α : UnitAddTorus (Fin k))
        (hα : α ∈ fordLemma63TorusOmega k M n u t) : A ≤ F α := by
      have hnLower : N ≤ n :=
        le_of_lt (Finset.mem_Ioc.mp hn).1
      dsimp [A, F]
      gcongr
      exact norm_fordLemma63T_le_SZeroTorus_on_box
        (by omega : 1 ≤ k) hM hN hnLower hu0 ht.le hscale hα
    have hconstInt : IntegrableOn (fun _ : UnitAddTorus (Fin k) => A)
        (fordLemma63TorusOmega k M n u t) μ :=
      integrableOn_const
    have hFintOn : IntegrableOn F (fordLemma63TorusOmega k M n u t) μ :=
      hFint.integrableOn
    have hmono := setIntegral_mono_on hconstInt hFintOn
      (measurableSet_fordLemma63TorusOmega k M n u t) hpoint
    rw [setIntegral_const, smul_eq_mul] at hmono
    have hvol : μ.real (fordLemma63TorusOmega k M n u t) = 1 / D := by
      dsimp [μ, D]
      exact fordLemma63TorusOmega_measure_exact (by omega : 1 ≤ k) hM
    rw [hvol] at hmono
    calc
      ‖fordLemma63T M n u t‖ ^ (2 * s) = A := rfl
      _ = D * ((1 / D) * A) := by field_simp [hDpos.ne']
      _ ≤ D * ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ :=
        mul_le_mul_of_nonneg_left hmono hDpos.le
  calc
    (∑ n ∈ Finset.Ioc N (2 * N - 1),
      ‖fordLemma63T M n u t‖ ^ (2 * s)) ≤
        ∑ n ∈ Finset.Ioc N (2 * N - 1),
          D * ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ := by
      apply Finset.sum_le_sum
      intro n hn
      exact hsingle n hn
    _ = D * (∑ n ∈ Finset.Ioc N (2 * N - 1),
        ∫ α in fordLemma63TorusOmega k M n u t, F α ∂μ) := by
      rw [Finset.mul_sum]
    _ ≤ D * (fordLemma63W N k M t * ∫ α, F α ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ hDpos.le
      exact fordLemma63_sum_setIntegral_le_W_mul
        hk hM hN hu0 hu1 ht htN hFint hFnonneg
    _ ≤ D * (fordLemma63W N k M t *
        ((2 : ℝ) ^ (4 * s) *
          (fordVinogradovMomentNat s k M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hDpos.le
      apply mul_le_mul_of_nonneg_left
      · exact fordLemma63_integral_SZeroTorus_two_s_le hs hM
      · unfold fordLemma63W
        positivity
    _ = _ := by
      dsimp [D]
      ring

#print axioms continuous_fordLemma63SZeroTorus
#print axioms integrable_fordLemma63SZeroTorus_pow
#print axioms exists_real_lift_mem_closedBall
#print axioms exists_real_lift_mem_fordLemma63Omega
#print axioms norm_fordLemma63T_le_SZeroTorus_on_box
#print axioms ford_equation_6_9

end

end GafniTao
