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
its interior. Ordinary reference jets and uniform perturbations are also
controlled on every positive compact interval. HuxleyLinearForms consumes
these tests in its constructed enlarged-phase source entry. Neither module
yet proves the parameter-family fifth moment or any new beta row.
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

private theorem compact_tests_uniform_lower {n m : ℕ} [Nonempty (Fin m)]
    (f : (Fin n → ℝ) → Fin m → ℝ)
    (hf : ∀ i, Continuous (fun v => f v i))
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSne : S.Nonempty)
    (hne : ∀ v ∈ S, ∀ i, f v i ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ w ∈ S, ∀ v : Fin n → ℝ, dist v w ≤ δ → ∀ i, c ≤ |f v i| := by
  let U := {v : Fin n → ℝ | ∀ i, f v i ≠ 0}
  have hU : IsOpen U := by
    have hi (i : Fin m) : IsOpen {v : Fin n → ℝ | f v i ≠ 0} :=
      isOpen_ne.preimage (hf i)
    simpa only [Set.iInter_setOf] using isOpen_iInter_of_finite hi
  obtain ⟨δ,hδ,hδU⟩ := hS.exists_cthickening_subset_open hU hne
  let K := cthickening δ S
  have hK : IsCompact K := hS.cthickening
  have hKne : K.Nonempty := hSne.mono (self_subset_cthickening S)
  have hc : Continuous (fun p : (Fin n → ℝ) × Fin m => |f p.1 p.2|) := by
    apply continuous_abs.comp
    apply continuous_prod_of_discrete_right.mpr
    exact hf
  obtain ⟨p,hp,hmin⟩ := (hK.prod (isCompact_univ : IsCompact (univ : Set (Fin m)))).exists_isMinOn
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

/-- The original seven tests are nonzero for the ordinary reference jets
at every positive point, not only inside the ANTEDB phase interval. -/
theorem reference_tests_positive {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) (i : Fin 7) :
    tests (fun j : Fin 4 => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x) i ≠ 0 := by
  have hj (n : ℕ) : iteratedDeriv n (Expdb.modelPhase σ) x =
      (descPochhammer ℝ n).eval (-σ)*x^(-σ-(n:ℝ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const (-σ) x n
  have hp (n : ℕ) (hn : n ≤ 5) :
      x^(-σ-(n:ℝ))=x^(5-n)*x^(-σ-5) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hx]
    congr 1
    rw [Nat.cast_sub hn]
    norm_num
  let z := σ*(σ+1)*x^(-σ-5)
  have he : (fun j : Fin 4 => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x) =
      ![z*x^3,-(σ+2)*z*x^2,(σ+2)*(σ+3)*z*x,-(σ+2)*(σ+3)*(σ+4)*z] := by
    funext j
    fin_cases j <;> dsimp only [z]
    all_goals
      rw [hj,hp _ (by norm_num)]
      norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
      ring
  rw [he]
  have hh := tests_monomial_ne_zero (a:=σ+2) (z:=z) (x:=x)
    (by linarith only [hσ]) (by dsimp only [z]; positivity) hx i
  simpa only [show σ+2+1=σ+3 by ring,show σ+2+2=σ+4 by ring] using hh

/-- One perturbation tolerance works for all seven tests on any fixed
positive compact interval. This reuses the existing compact jet argument. -/
theorem exists_uniform_test_lower_positive_compact
    {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ v : Fin 4 → ℝ,
        (∀ j, |v j-iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x| ≤ δ) →
        ∀ j, c ≤ |tests v j| := by
  let R := fun (x : ℝ) (j : Fin 4) => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x
  have hR : ContinuousOn R (Set.Icc a b) := by
    apply continuousOn_pi.mpr
    intro j x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (ha.trans_le hx.1).ne') (j.val+2)).continuousAt.continuousWithinAt
  let S := R '' Set.Icc a b
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn hR
  have hSne : S.Nonempty := ⟨R a,a,⟨le_rfl,hab⟩,rfl⟩
  have hn : ∀ v ∈ S, ∀ j, tests v j ≠ 0 := by
    rintro v ⟨x,hx,rfl⟩ j
    exact reference_tests_positive hσ (ha.trans_le hx.1) j
  obtain ⟨δ,c,hδ,hc,hlower⟩ := compact_tests_uniform_lower
    tests continuous_tests hS hSne hn
  refine ⟨δ,c,hδ,hc,?_⟩
  intro x hx v hv
  apply hlower _ (mem_image_of_mem R hx) v
  rw [dist_pi_le_iff hδ.le]
  exact hv

/-- The two literal Case 2 expressions in Huxley's Theorem 2.
Coordinates 0..3 are spatial jets 2..5; 4..6 are mixed jets (2,1)..(4,1). -/
def caseTwoTests (w : Fin 7 → ℝ) : Fin 2 → ℝ :=
  ![3*(w 1)^2-w 0*w 2,
    Matrix.det ![![3*(w 1)^2+4*w 0*w 2,3*w 0*w 1,(w 0)^2],
      ![w 3,w 2,w 1],![w 6,w 5,w 4]]]

/-- Retaining the parameter amplitude produces the original seven-test
determinant, with the required row swap and fourth scaling power. -/
theorem caseTwoTests_scaled (v : Fin 4 → ℝ) (y σ : ℝ) :
    caseTwoTests ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
      -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] =
      ![y^2/σ^2*HuxleyModel.tests v 5,-y^3/σ^4*HuxleyModel.tests v 6] := by
  funext j
  fin_cases j <;>
    simp [caseTwoTests,HuxleyModel.tests,Matrix.det_fin_three,div_eq_mul_inv] <;> ring

theorem continuous_caseTwoTests (j : Fin 2) :
    Continuous (fun w : Fin 7 → ℝ => caseTwoTests w j) := by
  fin_cases j <;> dsimp [caseTwoTests,Matrix.det_fin_three] <;> fun_prop


/-- Uniform robustness of the actual two Case 2 polynomials, before the
original phase or the small shift is selected. -/
theorem caseTwoTests_uniform_stability {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧
      ∀ (v : Fin 4 → ℝ) (y : ℝ),
      (∀ i, |v i| ≤ U) → c ≤ |HuxleyModel.tests v 5| → c ≤ |HuxleyModel.tests v 6| →
      y ∈ Icc (1:ℝ) 2 → ∀ w : Fin 7 → ℝ,
      (∀ i, |w i- ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
        -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] i| ≤ ε) →
      ∀ j, d ≤ |caseTwoTests w j| := by
  let A : Set (Fin 4 → ℝ) :=
    (Icc (fun _ => -U) (fun _ => U) ∩ {v | c ≤ |HuxleyModel.tests v 5|}) ∩
      {v | c ≤ |HuxleyModel.tests v 6|}
  have hA : IsCompact A :=
    (isCompact_Icc.inter_right
      (isClosed_le continuous_const (HuxleyModel.continuous_tests 5).abs)).inter_right
        (isClosed_le continuous_const (HuxleyModel.continuous_tests 6).abs)
  let ψ := fun p : (Fin 4 → ℝ) × ℝ =>
    ![-p.2/σ*p.1 0,-p.2/σ*p.1 1,-p.2/σ*p.1 2,-p.2/σ*p.1 3,
      -1/σ*p.1 0,-1/σ*p.1 1,-1/σ*p.1 2]
  have hψ : Continuous ψ := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp only [ψ] <;> fun_prop
  let S := ψ '' (A ×ˢ Icc (1:ℝ) 2)
  have hS : IsCompact S := (hA.prod isCompact_Icc).image hψ
  have hmem (v : Fin 4 → ℝ) y (hv : ∀ i, |v i| ≤ U)
      (h₅ : c ≤ |HuxleyModel.tests v 5|) (h₆ : c ≤ |HuxleyModel.tests v 6|)
      (hy : y ∈ Icc (1:ℝ) 2) : ψ (v,y) ∈ S := by
    apply mem_image_of_mem
    exact ⟨⟨⟨⟨fun i => (abs_le.mp (hv i)).1,fun i => (abs_le.mp (hv i)).2⟩,h₅⟩,h₆⟩,hy⟩
  by_cases hSne : S.Nonempty
  · have hn : ∀ w ∈ S, ∀ j, caseTwoTests w j ≠ 0 := by
      rintro w ⟨⟨v,y⟩,⟨hv,hy⟩,rfl⟩ j
      have hy0 : 0 < y := zero_lt_one.trans_le hy.1
      have hn₅ := abs_pos.mp (hc.trans_le hv.1.2)
      have hn₆ := abs_pos.mp (hc.trans_le hv.2)
      change caseTwoTests ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
        -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] j ≠ 0
      rw [caseTwoTests_scaled]
      fin_cases j
      · exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hy0.ne') (pow_ne_zero 2 hσ.ne')) hn₅
      · exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hy0.ne'))
          (pow_ne_zero 4 hσ.ne')) hn₆
    obtain ⟨ε,d,hε,hd,hstab⟩ := compact_tests_uniform_lower
      caseTwoTests continuous_caseTwoTests hS hSne hn
    refine ⟨ε,d,hε,hd,?_⟩
    intro v y hv h₅ h₆ hy w hw j
    apply hstab _ (hmem v y hv h₅ h₆ hy) w ?_ j
    rw [dist_pi_le_iff hε.le]
    exact hw
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro v y hv h₅ h₆ hy
    exfalso
    exact hSne ⟨_,hmem v y hv h₅ h₆ hy⟩

end TaoTrudgianYang2025.HuxleyModel
