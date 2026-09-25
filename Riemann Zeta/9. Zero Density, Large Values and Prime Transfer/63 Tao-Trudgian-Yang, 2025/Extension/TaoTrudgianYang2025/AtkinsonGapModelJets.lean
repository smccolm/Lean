import TaoTrudgianYang2025.AtkinsonGapNormalization
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# All fixed-order jets of the actual normalized Atkinson slope

Joint smoothness includes the zero perturbation and equal-height
parameters. Compactness chooses one perturbation radius before both
the height ratio and the summation coordinate.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace TaoTrudgianYang2025

theorem contDiffAt_atkinsonGapSlopeProfile_jet (n : ℕ)
    {q r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hqr : 0 < r+q*x) (hqx : 0 < 1+q*x) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ × ℝ =>
        iteratedDeriv n (atkinsonGapSlopeProfile p.1 p.2.1) p.2.2)
      (q,r,x) := by
  induction n generalizing q r x with
  | zero => simpa only [iteratedDeriv_zero] using
      contDiffAt_atkinsonGapSlopeProfile hr hx hqr hqx
  | succ n ih =>
    have hj := ih hr hx hqr hqx
    have hinner : ContDiffAt ℝ ∞
        (fun z : (ℝ × ℝ × ℝ) × ℝ =>
          iteratedDeriv n (atkinsonGapSlopeProfile z.1.1 z.1.2.1) z.2)
        ((q,r,x),x) :=
      hj.comp ((q,r,x),x)
        (f := fun z : (ℝ × ℝ × ℝ) × ℝ => (z.1.1,z.1.2.1,z.2))
        (by fun_prop)
    have hd := ContDiffAt.fderiv
      (f := fun p : ℝ × ℝ × ℝ =>
        fun y : ℝ => iteratedDeriv n (atkinsonGapSlopeProfile p.1 p.2.1) y)
      (g := fun p : ℝ × ℝ × ℝ => p.2.2)
      hinner (by fun_prop : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ × ℝ => p.2.2) (q,r,x))
      (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)
    have he := hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
    simpa only [iteratedDeriv_succ,fderiv_apply_one_eq_deriv] using he

theorem atkinsonGapSlopeProfile_jet_zero (n : ℕ) (r x : ℝ) :
    iteratedDeriv n (atkinsonGapSlopeProfile 0 r) x =
      iteratedDeriv n (fun y : ℝ => 1/Real.sqrt y) x := by
  congr 1
  funext y
  exact atkinsonGapSlopeProfile_zero r y

theorem atkinsonGapSlopeProfile_uniform_jet (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q r x : ℝ, |q| < δ →
      r ∈ Icc (1 : ℝ) 2 → x ∈ Icc (1 : ℝ) 2 →
      |iteratedDeriv n (atkinsonGapSlopeProfile q r) x-
        iteratedDeriv n (fun y : ℝ => 1/Real.sqrt y) x| < ε := by
  let f : ℝ × ℝ × ℝ → ℝ := fun p =>
    iteratedDeriv n (atkinsonGapSlopeProfile p.1 p.2.1) p.2.2
  let S : Set (ℝ × ℝ × ℝ) := {0} ×ˢ (Icc 1 2 ×ˢ Icc 1 2)
  have hS : IsCompact S := isCompact_singleton.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : ∀ p ∈ S, ContinuousAt f p := by
    rintro ⟨q,r,x⟩ ⟨hq,hr,hx⟩
    have hq0 : q = 0 := hq
    subst q
    exact (contDiffAt_atkinsonGapSlopeProfile_jet n
      (by linarith [hr.1]) (by linarith [hx.1])
      (by simpa using (show 0 < r by linarith [hr.1]))
      (by norm_num)).continuousAt
  have hu := hS.uniformContinuousAt_of_continuousAt f hc (Metric.dist_mem_uniformity hε)
  obtain ⟨δ,hδ,hbound⟩ := Metric.uniformity_basis_dist.mem_iff.mp hu
  refine ⟨δ,hδ,?_⟩
  intro q r x hq hr hx
  have hdist : dist ((0 : ℝ),r,x) (q,r,x) < δ := by
    simpa only [dist_prod_same_right,Real.dist_eq,zero_sub,abs_neg] using hq
  have h := @hbound (((0 : ℝ),r,x),(q,r,x)) hdist
    (show ((0 : ℝ),r,x) ∈ S from ⟨rfl,hr,hx⟩)
  change dist (iteratedDeriv n (atkinsonGapSlopeProfile 0 r) x)
    (iteratedDeriv n (atkinsonGapSlopeProfile q r) x) < ε at h
  rw [atkinsonGapSlopeProfile_jet_zero] at h
  simpa only [Real.dist_eq,abs_sub_comm] using h

theorem atkinsonGapSlopeProfile_uniform_finite_jets (P : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n ≤ P, ∀ q r x : ℝ, |q| < δ →
      r ∈ Icc (1 : ℝ) 2 → x ∈ Icc (1 : ℝ) 2 →
      |iteratedDeriv n (atkinsonGapSlopeProfile q r) x-
        iteratedDeriv n (fun y : ℝ => 1/Real.sqrt y) x| < ε := by
  induction P with
  | zero =>
    obtain ⟨δ,hδ,hb⟩ := atkinsonGapSlopeProfile_uniform_jet 0 hε
    refine ⟨δ,hδ,?_⟩
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    exact hb
  | succ P ih =>
    obtain ⟨δ,hδ,hb⟩ := ih
    obtain ⟨δ',hδ',hb'⟩ := atkinsonGapSlopeProfile_uniform_jet (P+1) hε
    refine ⟨min δ δ',lt_min hδ hδ',?_⟩
    intro n hn q r x hq hr hx
    by_cases hnP : n ≤ P
    · exact hb n hnP q r x (hq.trans_le (min_le_left _ _)) hr hx
    · have he : n = P+1 := by omega
      subst n
      exact hb' q r x (hq.trans_le (min_le_right _ _)) hr hx

end TaoTrudgianYang2025
