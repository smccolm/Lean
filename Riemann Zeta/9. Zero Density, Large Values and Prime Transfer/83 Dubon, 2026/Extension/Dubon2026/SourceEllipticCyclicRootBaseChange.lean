import Dubon2026.SourceEllipticTwoQuotientBaseChange
import Dubon2026.SourceEllipticPrimeCyclicRootMap

/-! DUB-17/18 -> original inertia -> good reduction -> cyclic orbit census.
The actual prime cyclic-root map commutes with field embeddings. The original
subgroups are transported by the native point map, their orders by injectivity,
and their root values by the already proved literal quotient formulas. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- Transport the original prime cyclic subgroup by the actual field point map. -/
def primeCyclicKernelMap (f : F →+* K) (W : WeierstrassCurve F) (p : ℕ)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    {H : AddSubgroup (W.map f).toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
  let h := SourceEllipticCyclicCount.isAddCyclic_map_and_card_of_injective p
    (pointMapHom f W) (pointMapHom_injective f W) H.2
  ⟨H.1.map (pointMapHom f W), h.1, h.2.1⟩

variable [IsAlgClosed F] [IsAlgClosed K]

/-- The odd-prime root value commutes with the original coefficient embedding. -/
theorem oddPrimeCyclicRootMap_map (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hpK : (p : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    (oddPrimeCyclicRootMap (W.map f) p hp2 hpK (primeCyclicKernelMap f W p H)).1 =
      f (oddPrimeCyclicRootMap W p hp2 hpF H).1 := by
  let P := primeKernelGenerator W p H
  have hP := primeKernelGenerator_oddOrder W p hp2 H
  have hP' : addOrderOf (pointMapHom f W P) = 2 * (p / 2) + 1 := by
    rw [addOrderOf_injective (pointMapHom f W) (pointMapHom_injective f W)]
    exact hP
  have hPH : AddSubgroup.zmultiples (pointMapHom f W P) =
      (primeCyclicKernelMap f W p H).1 := by
    change _ = H.1.map (pointMapHom f W)
    rw [← AddMonoidHom.map_zmultiples, primeKernelGenerator_zmultiples]
  rw [oddPrimeCyclicRootMap_eq_quotient (W.map f) p hp2 hpK _ hP' hPH]
  exact oddQuotientJ_map f W hP hP'

/-- The degree-two root value commutes with the original coefficient embedding. -/
theorem twoCyclicRootMap_map (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    (h2F : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2}) :
    (twoCyclicRootMap (W.map f) h2K (primeCyclicKernelMap f W 2 H)).1 =
      f (twoCyclicRootMap W h2F H).1 := by
  let P := primeKernelGenerator W 2 H
  have hP := primeKernelGenerator_order W 2 H
  have hP' : addOrderOf (pointMapHom f W P) = 2 := by
    rw [addOrderOf_injective (pointMapHom f W) (pointMapHom_injective f W)]
    exact hP
  have hPH : AddSubgroup.zmultiples (pointMapHom f W P) =
      (primeCyclicKernelMap f W 2 H).1 := by
    change _ = H.1.map (pointMapHom f W)
    rw [← AddMonoidHom.map_zmultiples, primeKernelGenerator_zmultiples]
  rw [twoCyclicRootMap_eq_quotient (W.map f) h2K _ hP' hPH]
  exact twoQuotientJ_map f W hP hP'

/-- The actual all-prime cyclic-root map is natural under field embeddings. -/
theorem primeCyclicRootMap_map (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hpF : (p : F) ≠ 0) (hpK : (p : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    (primeCyclicRootMap (W.map f) p hpK (primeCyclicKernelMap f W p H)).1 =
      f (primeCyclicRootMap W p hpF H).1 := by
  by_cases hp2 : p = 2
  · subst p
    simpa only [primeCyclicRootMap, dif_pos rfl] using twoCyclicRootMap_map f W hpF hpK H
  · simpa only [primeCyclicRootMap, dif_neg hp2] using
      oddPrimeCyclicRootMap_map f W p hp2 hpF hpK H

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
