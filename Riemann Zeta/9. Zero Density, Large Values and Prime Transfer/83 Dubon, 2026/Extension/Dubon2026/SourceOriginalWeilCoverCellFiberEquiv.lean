import Dubon2026.SourceCoverSheetFiberBijection
import Dubon2026.SourceOriginalWeilCoverCellLiftFamily

/-! DUB-17/18 -> pairing involution -> actual boundary-fiber equivalences.
Every point of an original radial carrier identifies its actual cover fiber
with the sheet indices. This is proved from the constructed exhaustive and
disjoint lifts and the actual base coordinate, not assumed as transport data. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem exists_cell_sheet_fiber_equiv (C : CellGeometry.Cell N) (J : Type*) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : J → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ j, C.R.K ⊆ (ζ j).target) →
      (∀ j z, z ∈ C.R.K → ((ζ j).symm z).restrict FF = C.ζ.symm z) →
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) →
      (∀ w, w.restrict FF ∈ C.carrier → ∃ j, w ∈ (ζ j).symm '' C.R.K) →
      ∀ z ∈ C.R.K,
        ∃ e : J ≃ {w : Place ℂ EE // w.restrict FF = C.ζ.symm z},
          ∀ j, (e j).1 = (ζ j).symm z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ hK hp hd hx z hz
  have hex (w : Place ℂ EE) (t : ℂ) (ht : t ∈ C.R.K)
      (hw : w.restrict FF = C.ζ.symm t) : ∃ j, (ζ j).symm t = w := by
    obtain ⟨j, u, hu, he⟩ := hx w ⟨t, ht, hw.symm⟩
    have hut : u = t := C.ζ.symm.injOn (C.hKt hu) (C.hKt ht)
      ((hp j u hu).symm.trans ((congrArg (fun P : Place ℂ EE => P.restrict FF) he).trans hw))
    exact ⟨j, by simpa only [hut] using he⟩
  have hb := SheetCover.sheet_fiber_bijective (fun P : Place ℂ EE => P.restrict FF)
    C.ζ ζ hK hp hd hex z hz
  exact ⟨Equiv.ofBijective _ hb, fun _ => rfl⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
