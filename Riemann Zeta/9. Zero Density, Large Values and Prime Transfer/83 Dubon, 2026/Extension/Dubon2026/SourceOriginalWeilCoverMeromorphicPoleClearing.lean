import Dubon2026.SourceOriginalWeilCoverMeromorphicPoleBound
import Dubon2026.SourceOriginalWeilCoverDimensionBounds
import Dubon2026.SourceOriginalWeilCoverReadFieldLaws

/-! DUB-17/18 -> auxiliary point division -> Abel converse -> actual field comparison.
Use the proved analytic pole bound and the actual finite-coordinate divisor
spaces to clear poles. The faithful basis relation then identifies the
analytic function in punctured chart germs with an element of the literal
Kummer splitting field. All cover geometry and dimension inputs are proved.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem exists_cover_meromorphic_pole_clearing
    (Q : Place ℂ (EE))
    (g : Place ℂ (EE) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N n r A hr hrA v z)) 0) :
    ∃ k : ℕ, ∃ h : EE, h ≠ 0 ∧
      ∀ v, MeromorphicAt ((fun z => g (placeFamily N n r A hr hrA v z)) * chartRead N n r A hr hrA v h) 0 ∧
        ((-(Finsupp.single Q (k : ℤ)) v : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt ((fun z => g (placeFamily N n r A hr hrA v z)) * chartRead N n r A hr hrA v h) 0 := by
  obtain ⟨E, _, hE⟩ := exists_cover_effective_meromorphic_pole_bound N n r A hr hrA g hg
  obtain ⟨k, h, hh0, hh⟩ := exists_cover_pole_clearing_function N n r Q E
  refine ⟨k, h, hh0, fun v => ?_⟩
  have hm := meromorphicAt_chartRead N n r A hr hrA v h (Metric.mem_ball_self (place_spec N n r A hr hrA v).1)
  refine ⟨(hg v).mul hm, ?_⟩
  have hl := add_le_add (hE v) (chartRead_lSpace_order_bound N n r A hr hrA _ hh v)
  rw [← WithTop.coe_add, ← meromorphicOrderAt_mul (hg v) hm] at hl
  have he : -E v + -(Finsupp.single Q (k : ℤ) - E) v =
      -(Finsupp.single Q (k : ℤ)) v := by
    simp only [Finsupp.sub_apply]
    ring
  rwa [he] at hl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
