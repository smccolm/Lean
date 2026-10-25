import Dubon2026.SourceCurveConvergentDiscResidues

/-! DUB-17/18 -> auxiliary cover charts -> meromorphic residue readings.
The actual residue evaluation equals the normal form throughout each family
disk. Its germs therefore have the exact normalized place orders, and every
regular reading is analytic. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*} [Field E] [Algebra ℂ E]
variable (e : E →ₐ[ℂ] realizedField) {R δ : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
variable (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
variable (hr : ∀ a, Represents (e a).val (G a))
variable (hv : ∀ P : Place ℂ E, Function.Bijective (algebraMap ℂ P.ResidueField))
variable (γ : ℂ → Place ℂ E) (hball : ∀ (z : ℂ), z ∈ ball 0 δ → z ∈ ball 0 R)
variable (hmem : ∀ z ∈ ball 0 δ, ∀ a,
  a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z)
variable (horder : ∀ z ∈ ball 0 δ, ∀ a, a ≠ 0 →
  meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ))
include hR hm hr hball hmem horder

theorem evaluation_germ (a : E) {z : ℂ} (hz : z ∈ ball 0 δ) :
    (fun t => (γ t).rationalEval (hv (γ t)) a) =ᶠ[𝓝 z] normal R G a := by
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact rationalEval_eq_normal e hR G hm hr (hball u hu) (γ u) (hv (γ u))
    (hmem u hu) (horder u hu) a

theorem evaluation_orders (a : E) (ha : a ≠ 0) {z : ℂ} (hz : z ∈ ball 0 δ) :
    MeromorphicAt (fun t => (γ t).rationalEval (hv (γ t)) a) z ∧
      meromorphicOrderAt (fun t => (γ t).rationalEval (hv (γ t)) a) z =
        ((γ z).ord a : WithTop ℤ) ∧
      (a ∈ (γ z).toValuationSubring →
        AnalyticAt ℂ (fun t => (γ t).rationalEval (hv (γ t)) a) z) := by
  have hg := evaluation_germ e hR G hm hr hv γ hball hmem horder a hz
  have hn : MeromorphicNFAt (fun t => (γ t).rationalEval (hv (γ t)) a) z :=
    (meromorphicNFAt_congr hg).mpr (normal_form G a (hball z hz))
  have ho : meromorphicOrderAt (fun t => (γ t).rationalEval (hv (γ t)) a) z =
      meromorphicOrderAt (G a) z := by
    rw [meromorphicOrderAt_congr (hg.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_congr (normal_germ hm a (hball z hz))]
  refine ⟨hn.meromorphicAt, ho.trans (horder z hz a ha), fun hm' => ?_⟩
  apply hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [ho]
  exact (hmem z hz a).mp hm'

end
end Dubon2026.SourceCurve.AnalyticDisc
