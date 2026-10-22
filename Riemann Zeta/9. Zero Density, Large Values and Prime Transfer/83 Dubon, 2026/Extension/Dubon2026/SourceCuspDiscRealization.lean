import Dubon2026.SourceCuspMeromorphicGerms

/-! DUB-17/18 -> original torsion cardinality -> cusp charts.
Functions meromorphic on one fixed disk and representing their actual
Laurent series form an intermediate field. Each analytic quotient has
such a disk; two original field generators will therefore supply one
common radius for the whole original function field.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter Metric
open scoped Topology

theorem Represents.meromorphicAt {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : Represents A F) : MeromorphicAt F 0 := by
  obtain ⟨f, g, hf, hg, _, _, he⟩ := hF
  exact (hf.meromorphicAt.div hg.meromorphicAt).congr he.symm

theorem Represents.order {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : Represents A F) (hA : A ≠ 0) :
    meromorphicOrderAt F 0 = (A.order : WithTop ℤ) := by
  obtain ⟨f, g, hf, hg, hg0, heA, heF⟩ := hF
  have hf0 : series f ≠ 0 := by
    intro hz
    apply hA
    rw [heA, hz, map_zero, zero_div]
  have hg0' : series g ≠ 0 := fun hz => hg0 (by rw [hz, map_zero])
  rw [meromorphicOrderAt_congr heF, meromorphicOrderAt_quotient hf hg hf0 hg0', ← heA]

/-- The actual Laurent series represented by meromorphic functions on this fixed disk. -/
def discField (R : ℝ) : IntermediateField ℂ (LaurentSeries ℂ) where
  carrier := {A | ∃ F : ℂ → ℂ, MeromorphicOn F (ball 0 R) ∧ Represents A F}
  zero_mem' := ⟨fun _ => 0, MeromorphicOn.const 0,
    by simpa only [map_zero] using represents_const 0⟩
  one_mem' := ⟨fun _ => 1, MeromorphicOn.const 1,
    by simpa only [map_one] using represents_const 1⟩
  add_mem' := by
    rintro A B ⟨F, hF, hFA⟩ ⟨G, hG, hGB⟩
    exact ⟨F + G, hF.add hG, hFA.add hGB⟩
  mul_mem' := by
    rintro A B ⟨F, hF, hFA⟩ ⟨G, hG, hGB⟩
    exact ⟨F * G, hF.mul hG, hFA.mul hGB⟩
  inv_mem' := by
    rintro A ⟨F, hF, hFA⟩
    exact ⟨F⁻¹, hF.inv, hFA.inv⟩
  algebraMap_mem' := fun c => ⟨fun _ => c, MeromorphicOn.const c, represents_const c⟩

theorem discField_mono {R S : ℝ} (hRS : R ≤ S) : discField S ≤ discField R := by
  rintro A ⟨F, hF, hFA⟩
  exact ⟨F, hF.mono_set (ball_subset_ball hRS), hFA⟩

theorem exists_discField_of_realized {A : LaurentSeries ℂ} (hA : RationallyRealized A) :
    ∃ R : ℝ, 0 < R ∧ A ∈ discField R := by
  obtain ⟨f, g, hf, hg, hg0, he⟩ := hA
  have hneigh : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z :=
    hf.eventually_analyticAt.and hg.eventually_analyticAt
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨R, hR, f / g, ?_, f, g, hf, hg, hg0, he, Filter.EventuallyEq.rfl⟩
  intro z hz
  exact (hball hz).1.meromorphicAt.div (hball hz).2.meromorphicAt

theorem order_ne_top_on_disc {A : LaurentSeries ℂ} {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : MeromorphicOn F (ball 0 R)) (hFA : Represents A F)
    (hA : A ≠ 0) {z : ℂ} (hz : z ∈ ball 0 R) : meromorphicOrderAt F z ≠ ⊤ := by
  apply hF.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) R).isPreconnected
    (mem_ball_self hR) hz
  rw [hFA.order hA]
  exact WithTop.coe_ne_top

end
end Dubon2026.SourceFunctionField.CuspTaylor
