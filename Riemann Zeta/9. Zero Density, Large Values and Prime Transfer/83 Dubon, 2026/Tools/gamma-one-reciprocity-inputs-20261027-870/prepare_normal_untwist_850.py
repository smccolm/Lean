from pathlib import Path
import hashlib,json
s=Path(__file__).parent
body=r"""import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> normalized invariant untwisting. Native meromorphic
normal forms replace a separate limit-based regularization. The order and
punctured germs are preserved exactly, including negative orders. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open Filter
open scoped Topology

theorem normalized_eq_of_analytic {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f U) (ha : a ∈ U) (han : AnalyticAt ℂ f a) :
    toMeromorphicNFOn f U =ᶠ[𝓝 a] f := by
  have he := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf ha
  rwa [toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt] at he

theorem normalized_eq_of_tendsto {U : Set ℂ} {f : ℂ → ℂ} {a c : ℂ}
    (hf : MeromorphicOn f U) (ha : a ∈ U) (h0 : meromorphicOrderAt f a = 0)
    (hc : Tendsto f (𝓝[≠] a) (𝓝 c)) :
    toMeromorphicNFOn f U a = c := by
  have hn := meromorphicNFOn_toMeromorphicNFOn f U ha
  have horder : meromorphicOrderAt (toMeromorphicNFOn f U) a = 0 := by
    rwa [meromorphicOrderAt_toMeromorphicNFOn hf ha]
  have han := hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp (le_of_eq horder.symm)
  exact tendsto_nhds_unique
    (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.congr' (hf.toMeromorphicNFOn_eq_self_on_nhdsNE ha).symm)

theorem normalized_eq_zero_of_order_ne_zero {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f U) (ha : a ∈ U) (h0 : meromorphicOrderAt f a ≠ 0) :
    toMeromorphicNFOn f U a = 0 := by
  by_contra hn
  have hz := (meromorphicNFOn_toMeromorphicNFOn f U ha).meromorphicOrderAt_eq_zero_iff.mpr hn
  exact h0 ((meromorphicOrderAt_toMeromorphicNFOn hf ha).symm.trans hz)

theorem normalized_local_form {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicOn f U) (ha : a ∈ U) (hn : meromorphicOrderAt f a = (n : WithTop ℤ)) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
      (f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ n * G z) ∧
      (toMeromorphicNFOn f U =ᶠ[𝓝 a] fun z => (z - a) ^ n * G z) := by
  have hnf := meromorphicNFOn_toMeromorphicNFOn f U ha
  rcases hnf with hz | ⟨m, G, hG, hG0, he⟩
  · have ht := meromorphicOrderAt_congr (hz.filter_mono nhdsWithin_le_nhds)
    rw [meromorphicOrderAt_toMeromorphicNFOn hf ha, hn] at ht
    simpa using ht
  · have hm : meromorphicOrderAt (toMeromorphicNFOn f U) a = (m : WithTop ℤ) :=
      (meromorphicOrderAt_eq_int_iff (meromorphicNFOn_toMeromorphicNFOn f U ha).meromorphicAt).mpr
        ⟨G, hG, hG0, he.filter_mono nhdsWithin_le_nhds⟩
    rw [meromorphicOrderAt_toMeromorphicNFOn hf ha, hn] at hm
    have hnm : n = m := WithTop.coe_inj.mp hm
    subst m
    have he' : toMeromorphicNFOn f U =ᶠ[𝓝 a] fun z => (z - a) ^ n * G z := by
      simpa only [Pi.smul_apply, Pi.pow_apply, smul_eq_mul] using he
    exact ⟨G, hG, hG0, (hf.toMeromorphicNFOn_eq_self_on_nhdsNE ha).symm.trans
      (he'.filter_mono nhdsWithin_le_nhds), he'⟩

theorem normalized_eventually_regular {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hU : IsOpen U) (hf : MeromorphicOn f U) (ha : a ∈ U)
    (hn : meromorphicOrderAt f a = (n : WithTop ℤ)) :
    ∀ᶠ z in 𝓝[≠] a, (f =ᶠ[𝓝 z] toMeromorphicNFOn f U) ∧
      AnalyticAt ℂ (toMeromorphicNFOn f U) z ∧ toMeromorphicNFOn f U z ≠ 0 := by
  obtain ⟨G, hG, hG0, -, he⟩ := normalized_local_form hf ha hn
  filter_upwards [(hf a ha).eventually_analyticAt,
    (hU.mem_nhds ha).filter_mono nhdsWithin_le_nhds,
    he.filter_mono nhdsWithin_le_nhds,
    (hG.continuousAt.eventually_ne hG0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzU hez hGz hza
  have heq := normalized_eq_of_analytic hf hzU hz
  refine ⟨heq.symm, hz.congr heq.symm, ?_⟩
  rw [hez]
  exact mul_ne_zero (zpow_ne_zero n (sub_ne_zero.mpr hza)) hGz

end
end Dubon2026.SourcePeriodUntwist
"""
with (s/'SourceMeromorphicNormalUntwist.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(body)
p=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\Analysis\Meromorphic\NormalForm.lean')
route=json.loads((s/'gamma-one-period-untwist-route-849.json').read_text(encoding='utf-8'))
route['reuseChecked'].append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest().upper()))
route['shorterRoute']='Use native toMeromorphicNFOn, preservation of meromorphic order and native normal-form local expansion. This replaces the primary custom limUnder regularization and most of its local normal-form proof. Original function germs, negative and positive integer orders, and nearby analytic nonvanishing are retained.'
with (s/'gamma-one-normal-untwist-route-850.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared native normalized germs for actual untwisting.')
