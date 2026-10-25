import Dubon2026.SourceCurveConvergentDiscUniformizer
import Dubon2026.SourceCurveOrderOnePlaces

/-! DUB-17/18 -> auxiliary cover analytic charts -> actual place families.
The order-one uniformizer differences give normalized places at nearby disk
points. Their center is the specified place, proved from its exact orders.
Chart injectivity, overlap compatibility and global geometry remain separate. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*} [Field E] [Algebra ℂ E]
variable (e : E →ₐ[ℂ] realizedField) {R : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
variable (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
variable (hr : ∀ a, Represents (e a).val (G a)) (w : Place ℂ E)
include hR hm hr

theorem exists_normalized_place {z : ℂ} (hz : z ∈ ball 0 R)
    (ha : AnalyticAt ℂ (normal R G w.uniformizer) z)
    (hd : deriv (normal R G w.uniformizer) z ≠ 0) :
    ∃ P : Place ℂ E,
      (∀ a, a ∈ P.toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z) ∧
      ∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = (P.ord a : WithTop ℤ) :=
  Place.exists_place_of_orderMap_of_order_one (fun a => meromorphicOrderAt (G a) z)
    (fun a => order_eq_top_iff e hR G hm hr a hz)
    (fun a b => order_mul e hR G hm hr a b hz)
    (fun a b => order_add e hR G hm hr a b hz)
    (fun c hc => order_const e hR G hm hr c hc hz)
    (w.uniformizer - algebraMap ℂ E (normal R G w.uniformizer z))
    (order_sub_uniformizer_one e hR G hm hr w hz ha hd)

theorem exists_place_family
    (ho : ∀ a, a ≠ 0 → meromorphicOrderAt (G a) 0 = (w.ord a : WithTop ℤ)) :
    ∃ (δ : ℝ) (γ : ℂ → Place ℂ E), 0 < δ ∧ γ 0 = w ∧
      ∀ z ∈ ball 0 δ, z ∈ ball 0 R ∧
        (∀ a, a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z) ∧
        (∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ)) ∧
        AnalyticAt ℂ (normal R G w.uniformizer) z ∧
        deriv (normal R G w.uniformizer) z ≠ 0 := by
  classical
  have hπ : meromorphicOrderAt (G w.uniformizer) 0 = (1 : ℤ) := by
    rw [ho _ w.uniformizer_ne_zero, w.ord_uniformizer]
  have hn := normal_uniformizer hR G hm w hπ
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 R := ball_mem_nhds 0 hR
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 R ∧
      AnalyticAt ℂ (normal R G w.uniformizer) z ∧
      deriv (normal R G w.uniformizer) z ≠ 0 :=
    hball.and
      (hn.1.eventually_analyticAt.and (hn.1.deriv.continuousAt.eventually_ne hn.2.2))
  obtain ⟨δ, hδ, hgood⟩ := Metric.eventually_nhds_iff_ball.mp he
  have hex (z : ℂ) (hz : z ∈ ball 0 δ) :=
    exists_normalized_place e hR G hm hr w (hgood z hz).1 (hgood z hz).2.1 (hgood z hz).2.2
  let γ : ℂ → Place ℂ E := fun z => if hz : z ∈ ball 0 δ then (hex z hz).choose else w
  have hγ (z : ℂ) (hz : z ∈ ball 0 δ) :
      (∀ a, a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z) ∧
      (∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ)) := by
    dsimp only [γ]
    rw [dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨δ, γ, hδ, ?_, fun z hz =>
    ⟨(hgood z hz).1, (hγ z hz).1, (hγ z hz).2, (hgood z hz).2.1, (hgood z hz).2.2⟩⟩
  apply Place.ext
  apply SetLike.ext
  intro a
  by_cases ha : a = 0
  · subst a
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · rw [(hγ 0 (mem_ball_self hδ)).1, w.mem_iff_ord_nonneg, ho a ha]
    exact WithTop.coe_nonneg

end
end Dubon2026.SourceCurve.AnalyticDisc
