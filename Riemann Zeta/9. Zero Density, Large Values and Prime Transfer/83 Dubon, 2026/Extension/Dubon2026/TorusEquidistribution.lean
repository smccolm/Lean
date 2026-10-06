import Dubon2026.PrimeTorus
import Mathlib.Topology.UrysohnsLemma

/-! # Continuous-test equidistribution of the prime torus flow

Fourier-mode convergence is extended through the uniform closure of their span.
The averaging functionals have norm at most one for every real height. This
argument concerns continuous tests only; singular logarithms need further work.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem integrable_torusHaar (N : ℕ) (f : C(PrimeTorus N, ℂ)) :
    Integrable f (torusHaar N) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem torusAverage_add (N : ℕ) (f g : C(PrimeTorus N, ℂ)) (T : ℝ) :
    torusAverage N (f + g) T = torusAverage N f T + torusAverage N g T :=
  symmetricAverage_add (f.continuous.comp (continuous_primeTorusFlow N))
    (g.continuous.comp (continuous_primeTorusFlow N)) T

theorem torusAverage_sub (N : ℕ) (f g : C(PrimeTorus N, ℂ)) (T : ℝ) :
    torusAverage N (f - g) T = torusAverage N f T - torusAverage N g T :=
  symmetricAverage_sub (f.continuous.comp (continuous_primeTorusFlow N))
    (g.continuous.comp (continuous_primeTorusFlow N)) T

theorem torusAverage_smul (N : ℕ) (c : ℂ) (f : C(PrimeTorus N, ℂ)) (T : ℝ) :
    torusAverage N (c • f) T = c • torusAverage N f T :=
  symmetricAverage_smul c _ T

theorem lipschitz_torusAverage (N : ℕ) (T : ℝ) :
    LipschitzWith 1 (fun f : C(PrimeTorus N, ℂ) => torusAverage N f T) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm, ← torusAverage_sub, NNReal.coe_one, one_mul] using
    norm_torusAverage_le N (f - g) T

theorem norm_torusHaar_integral_le (N : ℕ) (f : C(PrimeTorus N, ℂ)) :
    ‖∫ z, f z ∂torusHaar N‖ ≤ ‖f‖ := by
  simpa only [probReal_univ, mul_one] using
    MeasureTheory.norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm z) :
        ∀ᵐ z ∂torusHaar N, ‖f z‖ ≤ ‖f‖)

theorem lipschitz_torusHaar_integral (N : ℕ) :
    LipschitzWith 1 (fun f : C(PrimeTorus N, ℂ) => ∫ z, f z ∂torusHaar N) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hs : (∫ z, (f - g) z ∂torusHaar N) =
      (∫ z, f z ∂torusHaar N) - ∫ z, g z ∂torusHaar N :=
    integral_sub (integrable_torusHaar N f) (integrable_torusHaar N g)
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, hs] using
    norm_torusHaar_integral_le N (f - g)

theorem isClosed_torusAverage_convergence (N : ℕ) :
    IsClosed {f : C(PrimeTorus N, ℂ) |
      Tendsto (torusAverage N f) atTop (𝓝 (∫ z, f z ∂torusHaar N))} := by
  have he := LipschitzWith.uniformEquicontinuous
    (fun T (f : C(PrimeTorus N, ℂ)) => torusAverage N f T) 1 (lipschitz_torusAverage N)
  exact he.equicontinuous.isClosed_setOf_tendsto (lipschitz_torusHaar_integral N).continuous

theorem tendsto_torusAverage (N : ℕ) (f : C(PrimeTorus N, ℂ)) :
    Tendsto (torusAverage N f) atTop (𝓝 (∫ z, f z ∂torusHaar N)) := by
  let S := Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := PrimeCoordinate N)))
  have hs : (S : Set C(PrimeTorus N, ℂ)) ⊆
      {g | Tendsto (torusAverage N g) atTop (𝓝 (∫ z, g z ∂torusHaar N))} := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨k, rfl⟩ := hg
        exact tendsto_torusAverage_mFourier N k
    | zero =>
        change Tendsto (fun T => torusAverage N 0 T) atTop (𝓝 (∫ z, (0 : C(PrimeTorus N, ℂ)) z ∂torusHaar N))
        simpa only [torusAverage, ContinuousMap.zero_apply, symmetricAverage_zero,
          integral_zero] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add g h _ _ hg hh =>
        change Tendsto (fun T => torusAverage N (g + h) T) atTop
          (𝓝 (∫ z, (g + h) z ∂torusHaar N))
        have hi : (∫ z, (g + h) z ∂torusHaar N) =
            (∫ z, g z ∂torusHaar N) + ∫ z, h z ∂torusHaar N :=
          integral_add (integrable_torusHaar N g) (integrable_torusHaar N h)
        simpa only [hi, torusAverage_add] using hg.add hh
    | smul c g _ hg =>
        change Tendsto (fun T => torusAverage N (c • g) T) atTop
          (𝓝 (∫ z, (c • g) z ∂torusHaar N))
        have hi : (∫ z, (c • g) z ∂torusHaar N) = c • ∫ z, g z ∂torusHaar N :=
          integral_smul c g
        simpa only [hi, torusAverage_smul] using hg.const_smul c
  have hclosure : closure (S : Set C(PrimeTorus N, ℂ)) = Set.univ := by
    change (S.topologicalClosure : Set C(PrimeTorus N, ℂ)) = Set.univ
    rw [show S.topologicalClosure = ⊤ from UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  have hmem : f ∈ closure (S : Set C(PrimeTorus N, ℂ)) := by rw [hclosure]; trivial
  exact closure_minimal hs (isClosed_torusAverage_convergence N) hmem

theorem denseRange_primeTorusFlow (N : ℕ) : DenseRange (primeTorusFlow N) := by
  letI : Measure.IsOpenPosMeasure (torusHaar N) := by
    unfold torusHaar
    infer_instance
  intro z
  by_contra hz
  obtain ⟨g, hgzero, hgone, hgbound⟩ := exists_continuous_zero_one_of_isClosed
    isClosed_closure isClosed_singleton (Set.disjoint_singleton_right.mpr hz)
  let f : C(PrimeTorus N, ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have hfzero : (fun t => f (primeTorusFlow N t)) = fun _ => (0 : ℂ) := by
    funext t
    have hg := hgzero (subset_closure (Set.mem_range_self t))
    change (g (primeTorusFlow N t) : ℂ) = 0
    simp only [Pi.zero_apply] at hg
    rw [hg, Complex.ofReal_zero]
  have hlimzero : Tendsto (torusAverage N f) atTop (𝓝 (0 : ℂ)) := by
    change Tendsto (fun T => symmetricAverage (fun t => f (primeTorusFlow N t)) T) atTop (𝓝 0)
    simp only [hfzero, symmetricAverage_zero]
    exact tendsto_const_nhds
  have hint : (∫ x, f x ∂torusHaar N) = 0 :=
    tendsto_nhds_unique (tendsto_torusAverage N f) hlimzero
  have hgint : (∫ x, g x ∂torusHaar N) = 0 := by
    change (∫ x, (g x : ℂ) ∂torusHaar N) = 0 at hint
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hint
    exact hint
  have hpos : 0 < ∫ x, g x ∂torusHaar N :=
    integral_pos_of_integrable_nonneg_nonzero (x := z) g.continuous
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun x => (hgbound x).1) (by
        simpa only [hgone (Set.mem_singleton z), Pi.one_apply] using (one_ne_zero : (1 : ℝ) ≠ 0))
  exact (ne_of_gt hpos) hgint

end

end Dubon2026
