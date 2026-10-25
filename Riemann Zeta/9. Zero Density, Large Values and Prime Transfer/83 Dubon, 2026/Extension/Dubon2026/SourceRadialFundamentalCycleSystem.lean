import Dubon2026.SourceRadialDissectionPolygonWord
import Dubon2026.SourceCellIntegerFundamentalCycles

/-! DUB-17/18 -> cover reciprocity -> integer cycle system.
This is exactly the native fundamental-cycle conclusion on the actual
radial dissection. The theorem below applies the proved integer graph result;
the transparent proposition introduces no new geometric assumption. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
noncomputable section
open IntegerEdgeChains
variable {X : Type*} [TopologicalSpace X]

/-- The full integer cycle identities and universal additive decomposition. -/
abbrev FundamentalCycleSystem (D : RadialCellDissection X) (T : Finset D.ιE)
    (Z : D.ιE → D.ιE → ℤ) : Prop :=
      (∀ j w, (∑ e with (D.ends e).2 = w, Z j e) =
        (∑ e with (D.ends e).1 = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {B : Type*} [AddCommGroup B] (f : D.ιE → B),
        (∀ w, (∑ e with (D.ends e).2 = w, f e) =
          (∑ e with (D.ends e).1 = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j

theorem exists_fundamental_cycle_system (D : RadialCellDissection X) (T : Finset D.ιE)
    (hT : IsTree (hdΓ D) (tlΓ D) T) : ∃ Z, FundamentalCycleSystem D T Z :=
  exists_fundamental_cycles (hdΓ D) (tlΓ D) T hT

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
