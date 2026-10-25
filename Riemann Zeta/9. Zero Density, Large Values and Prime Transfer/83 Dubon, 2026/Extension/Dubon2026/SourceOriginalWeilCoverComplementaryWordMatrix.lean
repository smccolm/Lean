import Dubon2026.SourceOriginalWeilCoverComplementaryPeriodSpan
import Dubon2026.SourceRadialComplementaryWordMatrix
import Dubon2026.SourcePeriodMatrixLatticeUnimodularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! DUB-17/18 -> cover Abel converse -> exact integer matrix unimodularity.
The existing determinant theorem consumes actual jump-period rows, the reverse
generation from loops to jumps, the full real span and the proved Euler count.
Every one of these inputs is supplied by the actual cover construction. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders



open CellGeometry RadialDissectionPeriods

theorem cover_complementaryWordMatrix_isUnit {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE))
      (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ) (J : D.ιE → Fin kDim → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D (fun i => (b i : Ω[EE⁄ℂ])) V Ψ →
      IsJump D Ψ J → ∀ (T Ts : Finset D.ιE),
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) →
      AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)) →
      ∀ (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D (fun i => (b i : Ω[EE⁄ℂ])) T Ts γ →
      ∀ {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}),
      (∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
        (wordMatrix wd j l : ℂ) • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (γ l))) →
      IsUnit (complementaryWordMatrix T Ts wd).det := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D V Ψ J hP hJ T Ts hc hgen γ hR m hm wd hrow
  let z : {l // l ∈ (T ∪ Ts)ᶜ} → Fin kDim → ℂ :=
    fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (γ l.1)
  let Jc : {l // l ∈ (T ∪ Ts)ᶜ} → Fin kDim → ℂ := fun l => J l.1
  apply CellGeometry.DissectionPeriods.isUnit_det_of_lattice z Jc (complementaryWordMatrix T Ts wd)
  · intro j
    have hj : j.1 ∉ Ts := fun h => (Finset.mem_compl.mp j.2) (Finset.mem_union_right T h)
    rw [show Jc j = J j.1 from rfl, hrow j.1 hj, ← Finset.sum_coe_sort]
    simp only [complementaryWordMatrix, Int.cast_smul_eq_zsmul, z]
  · intro l
    have hm := hgen (cover_loop_period_mem_jumps N n radicand baseDivisor hRadicand hOrders D (fun i => (b i : Ω[EE⁄ℂ])) V Ψ J hP hJ
      (D.vert (D.ends l.1).1) (γ l.1))
    simpa only [Set.image_eq_range] using hm
  · exact cover_complementary_periods_span_real N n radicand baseDivisor hRadicand hOrders b D T Ts γ hR
  · have hn : Module.finrank ℂ (regularDifferentials ℂ EE) = kDim := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    simp only [Fintype.card_coe, hc, hn]
    simp [finrank_real_of_complex, two_mul]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
