import Dubon2026.SourceOriginalWeilCoverReadGerms

/-! DUB-17/18 -> auxiliary Abel converse -> actual function-field comparison.
Exact normalized orders make the actual cover chart germs faithful. Reuse
native residue field laws for inverses and finite linear combinations, and
transfer the actual divisor-space inequality to analytic vanishing orders.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem meromorphicOrderAt_chartRead (v : Place ℂ (EE))
    {f : EE} (hf : f ≠ 0) :
    meromorphicOrderAt (chartRead N n r A hr hrA v f) 0 = (v.ord f : WithTop ℤ) := by
  have h := ((place_spec N n r A hr hrA v).2.2.1 0 (Metric.mem_ball_self (place_spec N n r A hr hrA v).1) f hf).2.1
  rwa [(place_spec N n r A hr hrA v).2.1] at h

theorem eq_zero_of_chartRead_eventuallyEq_zero (v : Place ℂ (EE))
    {f : EE} (h : chartRead N n r A hr hrA v f =ᶠ[𝓝[≠] (0 : ℂ)] 0) : f = 0 := by
  by_contra hf
  have ho := meromorphicOrderAt_chartRead N n r A hr hrA v hf
  rw [meromorphicOrderAt_eq_top_iff.mpr h] at ho
  exact WithTop.top_ne_coe ho

theorem chartRead_eventually_ne_zero (v : Place ℂ (EE))
    {f : EE} (hf : f ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), chartRead N n r A hr hrA v f z ≠ 0 := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (meromorphicAt_chartRead N n r A hr hrA v f (Metric.mem_ball_self (place_spec N n r A hr hrA v).1))).mp
  rw [meromorphicOrderAt_chartRead N n r A hr hrA v hf]
  exact WithTop.coe_ne_top

theorem chartRead_smul (v : Place ℂ (EE))
    (c : ℂ) (f : EE) :
    chartRead N n r A hr hrA v (c • f) =ᶠ[𝓝[≠] (0 : ℂ)] c • chartRead N n r A hr hrA v f := by
  simpa only [Algebra.smul_def, chartRead_algebraMap, Pi.mul_def, Pi.smul_def,
    smul_eq_mul] using chartRead_mul N n r A hr hrA v (algebraMap ℂ (EE) c) f

theorem chartRead_neg (v : Place ℂ (EE))
    (f : EE) :
    chartRead N n r A hr hrA v (-f) =ᶠ[𝓝[≠] (0 : ℂ)] -chartRead N n r A hr hrA v f := by
  simpa only [neg_one_smul] using chartRead_smul N n r A hr hrA v (-1) f

theorem chartRead_inv (v : Place ℂ (EE))
    {f : EE} (hf : f ≠ 0) :
    chartRead N n r A hr hrA v f⁻¹ =ᶠ[𝓝[≠] (0 : ℂ)] (chartRead N n r A hr hrA v f)⁻¹ := by
  have h := chartRead_mul N n r A hr hrA v f⁻¹ f
  rw [inv_mul_cancel₀ hf, chartRead_one] at h
  filter_upwards [h] with z hz
  exact eq_inv_of_mul_eq_one_left hz.symm

theorem chartRead_sum_smul {ι : Type*} (s : Finset ι)
    (v : Place ℂ (EE)) (c : ι → ℂ)
    (f : ι → EE) :
    chartRead N n r A hr hrA v (∑ i ∈ s, c i • f i) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => ∑ i ∈ s, c i * chartRead N n r A hr hrA v (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, chartRead_zero]
    exact Eventually.of_forall fun _ => rfl
  | insert i s hi ih =>
    filter_upwards [ih, chartRead_add N n r A hr hrA v (c i • f i) (∑ j ∈ s, c j • f j),
      chartRead_smul N n r A hr hrA v (c i) (f i)] with z hz hadd hsmul
    rw [Finset.sum_insert hi, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
      smul_eq_mul, hz, Finset.sum_insert hi]

theorem chartRead_lSpace_order_bound
    (D : Divisor ℂ (EE))
    {f : EE} (hf : f ∈ LSpace D)
    (v : Place ℂ (EE)) :
    ((-D v : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (chartRead N n r A hr hrA v f) 0 := by
  have htop : meromorphicOrderAt (0 : ℂ → ℂ) (0 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun _ => rfl)
  rcases mem_lSpace_iff_ord.mp hf with rfl | h
  · rw [chartRead_zero, htop]
    exact le_top
  · by_cases hf0 : f = 0
    · rw [hf0, chartRead_zero, htop]
      exact le_top
    · rw [meromorphicOrderAt_chartRead N n r A hr hrA v hf0, WithTop.coe_le_coe]
      exact h v

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
