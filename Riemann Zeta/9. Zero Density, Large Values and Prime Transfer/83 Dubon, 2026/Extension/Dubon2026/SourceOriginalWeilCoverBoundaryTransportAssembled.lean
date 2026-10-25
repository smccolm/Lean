import Dubon2026.SourceOriginalWeilCoverArcSheetTransport

/-! DUB-17/18 -> lifted pairing -> constructed inverse sheet transport.
The actual cover cell families discharge every sheet, exhaustion, disjointness
and coordinate assumption in the endpoint-fiber transport. Only the original
base arc and its original reparameterization remain explicit source inputs. -/
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

theorem exists_cover_boundary_sheet_transport (C C' : CellGeometry.Cell N)
    (a b t₀ : ℝ) (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc a b))
    (hbase : ∀ t ∈ Icc a b, C'.bdry t = C.bdry (ψ t)) (ht₀ : t₀ ∈ Icc a b) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let I := {w : Place ℂ EE // w.restrict FF = C.ζ.symm C.R.q}
    let I' := {w : Place ℂ EE // w.restrict FF = C'.ζ.symm C'.R.q}
    ∃ (ζ : I → OpenPartialHomeomorph (Place ℂ EE) ℂ)
      (η : I' → OpenPartialHomeomorph (Place ℂ EE) ℂ) (T : I ≃ I'),
      (∀ i, C.R.K ⊆ (ζ i).target) ∧ (∀ j, C'.R.K ⊆ (η j).target) ∧
      (∀ i z, z ∈ C.R.K → ((ζ i).symm z).restrict FF = C.ζ.symm z) ∧
      (∀ j z, z ∈ C'.R.K → ((η j).symm z).restrict FF = C'.ζ.symm z) ∧
      (∀ i t, t ∈ Icc a b → (η (T i)).symm (C'.R.loop t) = (ζ i).symm (C.R.loop (ψ t))) ∧
      (∀ i P, P ∈ (ζ i).source →
        AnalyticAt ℂ (ζ i ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv (ζ i ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) ∧
      (∀ j P, P ∈ (η j).source →
        AnalyticAt ℂ (η j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv (η j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h1 := exists_cover_cell_lift_family N n radicand baseDivisor hRadicand hOrders C
  have h2 := exists_cover_cell_lift_family N n radicand baseDivisor hRadicand hOrders C'
  obtain ⟨V, ζ, _, _, _, hK, _, _, ht, hp, _, hd, hx, ha⟩ := h1
  obtain ⟨V', η, _, _, _, hK', _, _, ht', hp', _, hd', hx', ha'⟩ := h2
  have hζK : ∀ i, C.R.K ⊆ (ζ i).target := fun i z hz => by rw [(ht i).1]; exact hK hz
  have hηK : ∀ i, C'.R.K ⊆ (η i).target := fun i z hz => by rw [(ht' i).1]; exact hK' hz
  have hpζ : ∀ i z, z ∈ (ζ i).target → ((ζ i).symm z).restrict FF = C.ζ.symm z :=
    fun i z hz => hp i z (by rwa [← (ht i).1])
  have hpη : ∀ i z, z ∈ (η i).target → ((η i).symm z).restrict FF = C'.ζ.symm z :=
    fun i z hz => hp' i z (by rwa [← (ht' i).1])
  have htransport := exists_boundary_sheet_equiv N n radicand baseDivisor hRadicand hOrders
    C C' _ _ ζ η hζK hηK hpζ hpη hd hd' hx hx' a b t₀ ψ hψ hbase ht₀
  obtain ⟨T, hT⟩ := htransport
  exact ⟨ζ, η, T, hζK, hηK, fun i z hz => hp i z (hK hz),
    fun i z hz => hp' i z (hK' hz), hT, ha, ha'⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
