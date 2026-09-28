import TaoTrudgianYang2025.BetaModelJetEstimates
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Uniform model nondegeneracy for Huxley (1993), Theorem 3

The seven literal algebraic tests on printed pages 38--39 are derived from
ANTEDB's actual model-phase predicate, with a single perturbation tolerance
and positive lower constant chosen before the phase and point. The closed
interval uses within derivatives; the ordinary/logarithmic consumer is on
its interior. This proves neither the enlarged-domain bridge nor the
parameter-family fifth moment, resonance count, or any new beta row.
-/

noncomputable section

open Set Expdb Metric
open scoped ContDiff Topology

namespace TaoTrudgianYang2025.HuxleyModel

/-- The seven algebraic nonvanishing tests in Huxley (1993), Theorem 3.
The logarithmic tests are represented by their numerators, retaining the
nonzero derivative tests separately. Coordinates are derivatives 3 through 6. -/
def tests (v : Fin 4 → ℝ) : Fin 7 → ℝ :=
  ![v 0, v 1, v 2,
    v 0*v 2-(v 1)^2, v 1*v 3-(v 2)^2,
    3*(v 1)^2-v 0*v 2,
    Matrix.det ![![3*(v 1)^2+4*v 0*v 2,3*v 0*v 1,(v 0)^2],
      ![v 2,v 1,v 0],![v 3,v 2,v 1]]]

theorem tests_monomial (a z x : ℝ) :
    tests ![z*x^3,-a*z*x^2,a*(a+1)*z*x,-a*(a+1)*(a+2)*z] =
      ![z*x^3,-a*z*x^2,a*(a+1)*z*x,
        a*z^2*x^4,a^2*(a+1)*z^2*x^2,
        a*(2*a-1)*z^2*x^4,-a^2*(2*a-1)*z^4*x^8] := by
  funext i
  fin_cases i <;> simp [tests,Matrix.det_fin_three] <;> ring

theorem tests_monomial_ne_zero {a z x : ℝ}
    (ha : 1 < a) (hz : 0 < z) (hx : 0 < x) (i : Fin 7) :
    tests ![z*x^3,-a*z*x^2,a*(a+1)*z*x,-a*(a+1)*(a+2)*z] i ≠ 0 := by
  rw [tests_monomial]
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a+1 := by linarith
  have ha2 : 0 < 2*a-1 := by linarith
  fin_cases i <;> dsimp
  · positivity
  · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0.ne') hz.ne')
      (pow_ne_zero _ hx.ne')
  · positivity
  · positivity
  · positivity
  · positivity
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (neg_ne_zero.mpr (pow_ne_zero _ ha0.ne')) ha2.ne') (pow_ne_zero _ hz.ne'))
      (pow_ne_zero _ hx.ne')

theorem continuous_tests (i : Fin 7) : Continuous (fun v => tests v i) := by
  fin_cases i <;> simp [tests,Matrix.det_fin_three] <;> fun_prop

def referenceJets (σ x : ℝ) : Fin 4 → ℝ :=
  fun i => iteratedDerivWithin (i.val+2) (modelPhase σ) phaseInterval x

theorem referenceJets_eq {σ x : ℝ} (hx : x ∈ phaseInterval) :
    referenceJets σ x =
      let z := σ*(σ+1)*x^(-σ-5)
      ![z*x^3,-(σ+2)*z*x^2,(σ+2)*(σ+3)*z*x,
        -(σ+2)*(σ+3)*(σ+4)*z] := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hp (n : ℕ) (hn : n ≤ 5) :
      x^(-σ-(n:ℝ)) = x^(5-n)*x^(-σ-5) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hx0]
    congr 1
    rw [Nat.cast_sub hn]
    norm_num
  funext i
  fin_cases i <;> dsimp [referenceJets]
  all_goals
    rw [iteratedDerivWithin_modelPhase σ _ hx,hp _ (by norm_num)]
    norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
    ring

theorem reference_tests_ne_zero {σ : ℝ} (hσ : 0 < σ)
    {x : ℝ} (hx : x ∈ phaseInterval) (i : Fin 7) :
    tests (referenceJets σ x) i ≠ 0 := by
  rw [referenceJets_eq hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have h := tests_monomial_ne_zero (a := σ+2) (z := σ*(σ+1)*x^(-σ-5))
    (x := x) (by linarith) (by positivity) hx0 i
  simpa only [show σ+2+1=σ+3 by ring,show σ+2+2=σ+4 by ring] using h

theorem continuousOn_referenceJets (σ : ℝ) :
    ContinuousOn (referenceJets σ) phaseInterval := by
  apply continuousOn_pi.mpr
  intro i
  exact continuousOn_iteratedDerivWithin_modelPhase σ (i.val+2)

private theorem compact_tests_uniform_lower
    (f : (Fin 4 → ℝ) → Fin 7 → ℝ)
    (hf : ∀ i, Continuous (fun v => f v i))
    {S : Set (Fin 4 → ℝ)} (hS : IsCompact S) (hSne : S.Nonempty)
    (hne : ∀ v ∈ S, ∀ i, f v i ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ w ∈ S, ∀ v : Fin 4 → ℝ, dist v w ≤ δ → ∀ i, c ≤ |f v i| := by
  let U := {v : Fin 4 → ℝ | ∀ i, f v i ≠ 0}
  have hU : IsOpen U := by
    have hi (i : Fin 7) : IsOpen {v : Fin 4 → ℝ | f v i ≠ 0} :=
      isOpen_ne.preimage (hf i)
    simpa only [Set.iInter_setOf] using isOpen_iInter_of_finite hi
  obtain ⟨δ,hδ,hδU⟩ := hS.exists_cthickening_subset_open hU hne
  let K := cthickening δ S
  have hK : IsCompact K := hS.cthickening
  have hKne : K.Nonempty := hSne.mono (self_subset_cthickening S)
  have hc : Continuous (fun p : (Fin 4 → ℝ) × Fin 7 => |f p.1 p.2|) := by
    apply continuous_abs.comp
    apply continuous_prod_of_discrete_right.mpr
    exact hf
  obtain ⟨p,hp,hmin⟩ := (hK.prod (isCompact_univ : IsCompact (univ : Set (Fin 7)))).exists_isMinOn
    (hKne.prod (Set.univ_nonempty)) hc.continuousOn
  refine ⟨δ,|f p.1 p.2|,hδ,abs_pos.mpr (hδU hp.1 p.2),?_⟩
  intro w hw v hv j
  have hvK : v ∈ K := closedBall_subset_cthickening hw δ hv
  exact (isMinOn_iff.mp hmin) (v,j) ⟨hvK,mem_univ j⟩

/-- Uniform lower bounds for all seven tests throughout a fixed neighborhood
of the entire reference-jet curve. The constants precede every perturbed jet. -/
theorem exists_uniform_test_lower {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ x ∈ phaseInterval, ∀ v : Fin 4 → ℝ,
        (∀ i, |v i-referenceJets σ x i| ≤ δ) →
        ∀ j, c ≤ |tests v j| := by
  let S := referenceJets σ '' phaseInterval
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn
    (continuousOn_referenceJets σ)
  have hSne : S.Nonempty := ⟨referenceJets σ 1,1,by norm_num [phaseInterval],rfl⟩
  have hne : ∀ v ∈ S, ∀ i, tests v i ≠ 0 := by
    rintro v ⟨x,hx,rfl⟩ i
    exact reference_tests_ne_zero hσ hx i
  obtain ⟨δ,c,hδ,hc,h⟩ := compact_tests_uniform_lower tests continuous_tests hS hSne hne
  refine ⟨δ,c,hδ,hc,?_⟩
  intro x hx v hv
  have hdist : dist v (referenceJets σ x) ≤ δ := by
    rw [dist_pi_le_iff hδ.le]
    intro i
    exact hv i
  exact h _ (mem_image_of_mem _ hx) v hdist

theorem approximateModelPhase_tests_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ 5 δ →
        ∀ x ∈ phaseInterval, ∀ j,
          c ≤ |tests (fun i : Fin 4 => iteratedDerivWithin (i.val+3) F phaseInterval x) j| := by
  obtain ⟨δ,c,hδ,hc,h⟩ := exists_uniform_test_lower hσ
  refine ⟨δ,c,hδ,hc,?_⟩
  intro F hF x hx
  apply h x hx
  intro i
  have he := hF.2 (i.val+2) (by omega) ⟨x,hx⟩
  simpa only [modelPhaseErrorAt,referenceJets,Nat.add_assoc,Real.norm_eq_abs] using he

/-- Real.log differentiates as log absolute value for either sign, so the
negative fourth derivative introduces no extra sign assumption. -/
theorem iteratedDeriv_two_log_jet {F : ℝ → ℝ} {x : ℝ} (k : ℕ)
    (hF : ContDiffAt ℝ ∞ F x) (hne : iteratedDeriv k F x ≠ 0) :
    iteratedDeriv 2 (fun u => Real.log (iteratedDeriv k F u)) x =
      (iteratedDeriv k F x*iteratedDeriv (k+2) F x-
        (iteratedDeriv (k+1) F x)^2)/(iteratedDeriv k F x)^2 := by
  have hd {y : ℝ} (hy : ContDiffAt ℝ ∞ F y) (n : ℕ) :
      HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n+1) F y) y := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty hy n).differentiableAt (by simp)).hasDerivAt
  have hg : ContinuousAt (iteratedDeriv k F) x := (hd hF k).continuousAt
  have hg1 : ContDiffAt ℝ 1 (iteratedDeriv k F) x :=
    (contDiffAt_iteratedDeriv_infty hF k).of_le (by simp)
  have he : deriv (fun u => Real.log (iteratedDeriv k F u)) =ᶠ[𝓝 x]
      (fun u => iteratedDeriv (k+1) F u / iteratedDeriv k F u) := by
    filter_upwards [hg1.eventually (by simp), hg.eventually_ne hne] with y hy hny
    simpa only [← iteratedDeriv_succ] using
      ((hy.differentiableAt (by simp)).hasDerivAt.log hny).deriv
  have hq := ((hd hF (k+1)).div (hd hF k) hne).deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  convert hq using 1
  ring

/-- The literal ordinary-derivative tests on the interior, including both
logarithmic second derivatives from (12.2). No exponential-sum bound is claimed. -/
theorem approximateModelPhase_source_tests {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ 5 δ →
        ∀ x ∈ Ioo (1 : ℝ) 2,
          (∀ j, c ≤ |tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F x) j|) ∧
          (∀ r : ℕ, 3 ≤ r → r ≤ 4 →
            iteratedDeriv 2 (fun u => Real.log (iteratedDeriv r F u)) x ≠ 0) := by
  obtain ⟨δ,c,hδ,hc,h⟩ := approximateModelPhase_tests_uniform hσ
  refine ⟨δ,c,hδ,hc,?_⟩
  intro F hF x hx
  have hxI : x ∈ phaseInterval := ⟨hx.1.le,hx.2.le⟩
  have hFx : ContDiffAt ℝ ∞ F x := approximateModelPhase_contDiffAt hF hx
  have he (n : ℕ) : iteratedDerivWithin n F phaseInterval x = iteratedDeriv n F x :=
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
      (hFx.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) hxI
  have ht (j : Fin 7) : c ≤ |tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F x) j| := by
    simpa only [he] using h F hF x hxI j
  refine ⟨ht,?_⟩
  have h3 : iteratedDeriv 3 F x ≠ 0 := abs_pos.mp (hc.trans_le (ht 0))
  have h4 : iteratedDeriv 4 F x ≠ 0 := abs_pos.mp (hc.trans_le (ht 1))
  intro r hr hr'
  interval_cases r
  · rw [iteratedDeriv_two_log_jet 3 hFx h3]
    exact div_ne_zero (abs_pos.mp (hc.trans_le (ht 3))) (pow_ne_zero _ h3)
  · rw [iteratedDeriv_two_log_jet 4 hFx h4]
    exact div_ne_zero (abs_pos.mp (hc.trans_le (ht 4))) (pow_ne_zero _ h4)


/-- The same seven lower bounds hold for every actual compressed A-process
shift, with the tolerance and maximum shift chosen before the source phase.
This uses the existing domain-preserving shift theorem, not a hypothetical
shifted model. It does not supply mixed derivatives in the shift parameter. -/
theorem aProcessShiftPhase_tests_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ η₀ c : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧ 0 < c ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ 6 δ →
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ x ∈ phaseInterval, ∀ j,
          c ≤ |tests (fun i : Fin 4 => iteratedDerivWithin (i.val+3)
            (aProcessShiftPhase F σ η) phaseInterval x) j| := by
  obtain ⟨ε,c,hε,hc,htests⟩ := approximateModelPhase_tests_uniform
    (show 0 < σ+1 by linarith)
  obtain ⟨δ,η₀,hδ,hη₀,hhalf,hshift⟩ := aProcessShiftPhase_uniform_model hσ 5 hε
  refine ⟨δ,η₀,c,hδ,hη₀,hhalf,hc,?_⟩
  intro F hF η hη hηmax
  exact htests _ (hshift F η hF hη hηmax)

end TaoTrudgianYang2025.HuxleyModel

