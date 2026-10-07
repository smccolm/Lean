import Dubon2026.DirichletDivisor

/-! # Analytic weights and the genuine simple-pole residues of the logarithmic derivative -/

namespace Dubon2026

open Filter Complex Set
open scoped Topology

/-- A meromorphic function with order at least minus one has its actual simple-pole limit. -/
theorem tendsto_mul_sub_of_simple_order {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f p) :
    Tendsto (fun s => (s - p) * f s) (𝓝[≠] p) (𝓝 (residue f p)) := by
  have hl : MeromorphicAt (fun s : ℂ => s - p) p := by fun_prop
  have hm : MeromorphicAt (fun s => (s - p) * f s) p := hl.mul hf
  have hh : 0 ≤ meromorphicOrderAt (fun s => (s - p) * f s) p := by
    change 0 ≤ meromorphicOrderAt ((fun s : ℂ => s - p) * f) p
    rw [meromorphicOrderAt_mul hl hf, meromorphicOrderAt_id_sub_const]
    calc
      (0 : WithTop ℤ) = 1 + (-1) := by norm_num
      _ ≤ 1 + meromorphicOrderAt f p := add_le_add le_rfl ho
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm hh
  rwa [residue_eq_of_tendsto hc]

theorem weighted_dirichlet_logDeriv_simple {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) :
    (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (fun s => g s * logDeriv (dirichletSum a N) s) p := by
  have hf : MeromorphicOn (dirichletSum a N) Set.univ :=
    fun s _ => (analyticAt_dirichletSum a N s).meromorphicAt
  have hl := logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hf hf.logDeriv
    (fun s _ => meromorphicOrderAt_dirichletSum_ne_top hN ha s) p (mem_univ p)
  change (-1 : WithTop ℤ) ≤ meromorphicOrderAt (g * logDeriv (dirichletSum a N)) p
  rw [meromorphicOrderAt_mul hg.meromorphicAt (hf.logDeriv p (mem_univ p))]
  calc
    (-1 : WithTop ℤ) = 0 + (-1) := by simp
    _ ≤ meromorphicOrderAt g p + meromorphicOrderAt (logDeriv (dirichletSum a N)) p :=
      add_le_add hg.meromorphicOrderAt_nonneg hl

theorem residue_weighted_dirichlet_logDeriv {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) :
    residue (fun s => g s * logDeriv (dirichletSum a N) s) p =
      g p * (zeroMultiplicity a N p : ℂ) := by
  have hf : MeromorphicOn (dirichletSum a N) Set.univ :=
    fun s _ => (analyticAt_dirichletSum a N s).meromorphicAt
  have hl := logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hf hf.logDeriv
    (fun s _ => meromorphicOrderAt_dirichletSum_ne_top hN ha s) p (mem_univ p)
  have ht := tendsto_mul_sub_of_simple_order (hf.logDeriv p (mem_univ p)) hl
  have hr := logDeriv_residue_eq_meromorphicOrderAt (hf p (mem_univ p))
    (meromorphicOrderAt_dirichletSum hN ha p)
  simp only [Int.cast_natCast] at hr
  rw [hr] at ht
  apply residue_eq_of_tendsto
  convert hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.mul ht using 1
  funext s
  ring

theorem analyticAt_weighted_dirichlet_logDeriv {a : ℕ → ℂ} {N : ℕ}
    {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hn : dirichletSum a N p ≠ 0) :
    AnalyticAt ℂ (fun s => g s * logDeriv (dirichletSum a N) s) p := by
  exact hg.mul ((analyticAt_dirichletSum a N p).deriv.div
    (analyticAt_dirichletSum a N p) hn)

end Dubon2026
