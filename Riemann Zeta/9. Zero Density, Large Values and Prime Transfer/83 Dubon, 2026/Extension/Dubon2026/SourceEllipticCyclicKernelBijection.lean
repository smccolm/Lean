import Dubon2026.SourceEllipticCompositeQuotientJ

/-! The actual cyclic kernels transport bijectively between algebraically
closed models at every invertible level. The existing exact psi(N) count
and injectivity of the original point maps suffice. A separate construction
lifting every torsion point is unnecessary for this all-level root transport. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount SourceLevelProjective
open SourceFunctionField.IntegralJCoordinate OddDiscriminant SourceEllipticVariableChange
noncomputable section
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
variable [IsAlgClosed F] [IsAlgClosed L]

/-- The original field point map bijects all cyclic kernels of every invertible order. -/
theorem cyclicKernelMap_bijective (f : F →+* L) (W : WeierstrassCurve F) [W.IsElliptic]
    (N : ℕ) (hN : (N : F) ≠ 0) : Function.Bijective (primeCyclicKernelMap f W N) := by
  have hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hN
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have hs : Nat.card {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} =
      dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (actual_cyclic_subgroup_cardinality (F := F) (K := F) W hN)
  have ht : Nat.card {H : AddSubgroup (W.map f).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} =
      dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (actual_cyclic_subgroup_cardinality (F := L) (K := L) (W.map f) hNL)
  letI : Finite {H : AddSubgroup (W.map f).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    Nat.finite_of_card_ne_zero (ht.trans_ne (dedekindPsi_pos hN0).ne')
  have hinj : Function.Injective (primeCyclicKernelMap f W N) := by
    intro H H' he
    apply Subtype.ext
    exact AddSubgroup.map_injective (pointMapHom_injective f W) (congrArg Subtype.val he)
  exact hinj.bijective_of_nat_card_le (by rw [hs, ht])

/-- The original variable change bijects all actual cyclic kernels at every invertible order. -/
theorem cyclicKernelVariableChange_bijective
    (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0) :
    Function.Bijective (cyclicKernelVariableChange C W N) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have hs : Nat.card {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} =
      dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (actual_cyclic_subgroup_cardinality (F := F) (K := F) W hN)
  have ht : Nat.card {H : AddSubgroup (C • W).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} =
      dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (actual_cyclic_subgroup_cardinality (F := F) (K := F) (C • W) hN)
  letI : Finite {H : AddSubgroup (C • W).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    Nat.finite_of_card_ne_zero (ht.trans_ne (dedekindPsi_pos hN0).ne')
  have hinj : Function.Injective (cyclicKernelVariableChange C W N) := by
    intro H H' he
    apply Subtype.ext
    exact AddSubgroup.map_injective (variableChangeAddEquiv C W.toAffine).symm.injective
      (congrArg Subtype.val he)
  exact hinj.bijective_of_nat_card_le (by rw [hs, ht])

end
end Dubon2026.SourceEllipticVelu
