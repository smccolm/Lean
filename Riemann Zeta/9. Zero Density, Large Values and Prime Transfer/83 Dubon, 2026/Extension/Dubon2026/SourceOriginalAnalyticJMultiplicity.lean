import Dubon2026.SourceAnalyticJLocalOrders
import Dubon2026.SourceOriginalFiniteFiberOrbits

/-! DUB-17/18 -> numerical modular genus -> actual finite ramification.
The analytic multiplicity theorem is applied to the original j generator,
using its proved realization and normalized place order. The stabilizer
formula is derived from analytic orders; it is not a dictionary assumption.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem originalAnalyticOrder_j_sub (N : ℕ) [NeZero N] (τ : ℍ) (c : ℂ) :
    originalAnalyticOrder N τ
      (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =
      meromorphicOrderAt (fun z : ℂ => JMultiplicity.jf (ofComplex z) - c) (τ : ℂ) := by
  unfold originalAnalyticOrder
  apply meromorphicOrderAt_congr
  have he : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c =
      jOver N ℂ + algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [original_realize_add_eventuallyEq N (jOver N ℂ)
    (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) τ] with z hz
  have hconst : realize N
      ((algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) : modularFunctionFieldOver N ℂ) :
        LaurentSeries ℂ) (ofComplex z) = -c := realize_algebraMap N (-c) (ofComplex z)
  simpa only [realize_jOver, hconst, Pi.add_apply,
    sub_eq_add_neg, JMultiplicity.jf] using hz

theorem original_analytic_j_multiplicity (N : ℕ) [NeZero N] (τ : ℍ) :
    (((originalAnalyticRamification N τ : ℤ) *
      (originalAnalyticPlace N τ).ord (jOver N ℂ -
        algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) : ℤ) : WithTop ℤ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by
  have hx : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ) ≠ 0 := by
    intro he
    apply original_j_sub_transcendental N ℂ (JMultiplicity.jf τ)
    rw [he]
    exact isAlgebraic_zero
  rw [← originalAnalyticPlace_order N τ _ hx, originalAnalyticOrder_j_sub]
  exact JMultiplicity.main τ

theorem originalAnalyticRamification_dvd_full_stabilizer_half (N : ℕ) [NeZero N] (τ : ℍ) :
    originalAnalyticRamification N τ ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 := by
  have he := original_analytic_j_multiplicity N τ
  have hi : (originalAnalyticRamification N τ : ℤ) *
      (originalAnalyticPlace N τ).ord (jOver N ℂ -
        algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ)) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) :=
    WithTop.coe_injective he
  have hd : (originalAnalyticRamification N τ : ℤ) ∣
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := ⟨_, hi.symm⟩
  exact_mod_cast hd

end
end Dubon2026.SourceFunctionField
