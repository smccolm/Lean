import Dubon2026.SourceOriginalWeilCoverPathPrimitiveJumps
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! DUB-17/18 -> cover Abel converse -> actual regular loop generation.
The proved path-to-jump comparison and actual jump-period containment give
common integer coefficients for all differentials of the finite family.
Reuse native integer-span membership, without period-lattice discreteness. -/
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

theorem cover_loop_period_mem_jumps {κ : Type*} [Finite κ] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
      (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ → IsJump D Ψ J →
      ∀ (P : Place ℂ EE) (δ : Path P P),
      (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ) ∈
        AddSubgroup.closure (range J) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ P δ
  choose g hg using fun i => exists_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (η i) (hP.2.2.2.2 i) δ
  have hm := cover_path_sub_mem_closure_jumps N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ δ g hg
  simp only [sub_self, sub_zero] at hm
  have he : (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ) = fun i => g i 1 - g i 0 := by
    funext i
    exact pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (hg i)
  rw [he]
  exact hm

/-- Every actual regular loop period has common integer coefficients in the
same complementary cycles. The existence consumer proves this property. -/
def CoverRegularCycleGeneration {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (κ → Ω[EE⁄ℂ]) →
      Finset D.ιE → Finset D.ιE →
      ((j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η T Ts γ => ∀ (P : Place ℂ EE) (δ : Path P P), ∃ a : D.ιE → ℤ, ∀ i,
    pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ =
      ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)

theorem cover_regular_cycle_generation {κ : Type*} [Finite κ] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
      (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ → IsJump D Ψ J →
      ∀ (T Ts : Finset D.ιE)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      AddSubgroup.closure (range J) ≤ AddSubgroup.closure
        ((fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) ''
          ((T ∪ Ts)ᶜ : Finset D.ιE)) →
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D η T Ts γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts γ hcl P δ
  have hm := hcl (cover_loop_period_mem_jumps N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ P δ)
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun i => ?_⟩
  have hi := congrFun ha i
  simpa only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] using hi.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
