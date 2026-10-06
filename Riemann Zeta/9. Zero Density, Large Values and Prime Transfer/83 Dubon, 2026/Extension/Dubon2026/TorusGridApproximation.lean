import Dubon2026.TorusGridAverage

/-! # Uniform approximation of Haar averages by finite torus grids -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The constant continuous function equal to a Haar integral. -/
def torusHaarConstant (N : ℕ) (f : C(PrimeTorus N, ℂ)) : C(PrimeTorus N, ℂ) :=
  ContinuousMap.const _ (∫ z, f z ∂torusHaar N)

theorem torusHaarConstant_add (N : ℕ) (f g : C(PrimeTorus N, ℂ)) :
    torusHaarConstant N (f + g) = torusHaarConstant N f + torusHaarConstant N g := by
  ext z
  exact integral_add (integrable_torusHaar N f) (integrable_torusHaar N g)

theorem torusHaarConstant_smul (N : ℕ) (c : ℂ) (f : C(PrimeTorus N, ℂ)) :
    torusHaarConstant N (c • f) = c • torusHaarConstant N f := by
  ext z
  exact integral_smul c f

theorem lipschitz_torusHaarConstant (N : ℕ) : LipschitzWith 1 (torusHaarConstant N) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hd : torusHaarConstant N f - torusHaarConstant N g =
      ContinuousMap.const _ ((∫ z, f z ∂torusHaar N) - ∫ z, g z ∂torusHaar N) := rfl
  simp only [dist_eq_norm, hd, NNReal.coe_one, one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg (f - g))).mpr
  intro z
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ContinuousMap.const_apply] using
    (lipschitz_torusHaar_integral N).dist_le_mul f g

theorem isClosed_torusGridAverage_convergence (N : ℕ) :
    IsClosed {f : C(PrimeTorus N, ℂ) |
      Tendsto (fun n : ℕ => torusGridAverage N (n + 1) f) atTop (𝓝 (torusHaarConstant N f))} := by
  have he := LipschitzWith.uniformEquicontinuous
    (fun n (f : C(PrimeTorus N, ℂ)) => torusGridAverage N (n + 1) f) 1
    (fun n => lipschitz_torusGridAverage N (n + 1))
  exact he.equicontinuous.isClosed_setOf_tendsto (lipschitz_torusHaarConstant N).continuous

theorem tendsto_torusGridAverage (N : ℕ) (f : C(PrimeTorus N, ℂ)) :
    Tendsto (fun n : ℕ => torusGridAverage N (n + 1) f) atTop (𝓝 (torusHaarConstant N f)) := by
  let S := Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := PrimeCoordinate N)))
  have hs : (S : Set C(PrimeTorus N, ℂ)) ⊆
      {g | Tendsto (fun n : ℕ => torusGridAverage N (n + 1) g) atTop (𝓝 (torusHaarConstant N g))} := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_torusGridAverage_mFourier N k] with n hn
      exact hn.symm
    | zero =>
      change Tendsto (fun n : ℕ => torusGridAverage N (n + 1) 0) atTop
        (𝓝 (torusHaarConstant N 0))
      have hz (n : ℕ) : torusGridAverage N (n + 1) 0 = 0 := torusGridAverage_const N (n + 1) 0
      simpa only [hz, torusHaarConstant, ContinuousMap.zero_apply, integral_zero] using
        (tendsto_const_nhds (x := (0 : C(PrimeTorus N, ℂ))))
    | add g h _ _ hg hh =>
      change Tendsto (fun n : ℕ => torusGridAverage N (n + 1) (g + h)) atTop
        (𝓝 (torusHaarConstant N (g + h)))
      simpa only [torusGridAverage_add, torusHaarConstant_add] using hg.add hh
    | smul c g _ hg =>
      change Tendsto (fun n : ℕ => torusGridAverage N (n + 1) (c • g)) atTop
        (𝓝 (torusHaarConstant N (c • g)))
      simpa only [torusGridAverage_smul, torusHaarConstant_smul] using hg.const_smul c
  have hclosure : closure (S : Set C(PrimeTorus N, ℂ)) = Set.univ := by
    change (S.topologicalClosure : Set C(PrimeTorus N, ℂ)) = Set.univ
    rw [show S.topologicalClosure = ⊤ from UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  have hmem : f ∈ closure (S : Set C(PrimeTorus N, ℂ)) := by rw [hclosure]; trivial
  exact closure_minimal hs (isClosed_torusGridAverage_convergence N) hmem

theorem eventually_torusGridAverage_uniform (N : ℕ) (f : C(PrimeTorus N, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : PrimeTorus N,
      ‖torusGridAverage N (n + 1) f z - (∫ w, f w ∂torusHaar N)‖ < ε := by
  have h := (Metric.tendsto_nhds.mp (tendsto_torusGridAverage N f)) ε hε
  filter_upwards [h] with n hn
  intro z
  exact ((torusGridAverage N (n + 1) f - torusHaarConstant N f).norm_coe_le_norm z).trans_lt
    (by simpa only [dist_eq_norm] using hn)

end

end Dubon2026
