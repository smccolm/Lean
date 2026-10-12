import Dubon2026.CoinducedCosetValues
import Dubon2026.CosetTransitionCoordinates

/-! # The original finite coinduced coefficient action is continuous

The existing coinduced object is retained. Its genuine finite coset values
prove finiteness and continuity of the action, supplying the coefficient input
for continuous Shapiro comparison in DUB-17's finite-module local duality.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The original coinduced coefficient is determined by its actual coset values. -/
theorem coinducedCosetValues_injective : Function.Injective (coinducedCosetValues A S) := by
  intro f h he
  apply Subtype.ext
  funext g
  have hv := congrArg (fun z : G ⧸ S → A => z (QuotientGroup.mk g⁻¹)) he
  have ht := congrArg (fun z : A => A.ρ g z) hv
  change A.ρ g (A.ρ g⁻¹ (f.val g⁻¹⁻¹)) = A.ρ g (A.ρ g⁻¹ (h.val g⁻¹⁻¹)) at ht
  simpa only [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using ht

/-- The actual coinduced module is finite when its original coefficients and
actual subgroup cosets are finite. -/
theorem coinducedCoefficient_finite [Finite A] [Finite (G ⧸ S)] :
    Finite (Rep.coind S.subtype (Rep.res S.subtype A)) :=
  Finite.of_injective _ (coinducedCosetValues_injective A S)

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [Finite (G ⧸ S)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))

include hA hS in
/-- The original finite coinduced action is jointly continuous. Evaluation uses
the existing exact coset-action identity and the original open-subgroup topology. -/
theorem finiteCoinducedCoefficientAction_continuous :
    Continuous (fun z : G × Rep.coind S.subtype (Rep.res S.subtype A) =>
      (Rep.coind S.subtype (Rep.res S.subtype A)).ρ z.1 z.2) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have he : Topology.IsEmbedding (coinducedCosetValues A S) :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
      (coinducedCosetValues_injective A S) (fun _ _ => isOpen_discrete _)).isEmbedding
  apply he.continuous_iff.mpr
  apply continuous_pi
  intro q
  have hv : Continuous (fun z : Rep.coind S.subtype (Rep.res S.subtype A) × (G ⧸ S) =>
      coinducedCosetValues A S z.1 z.2) := continuous_of_discreteTopology
  have ht := hA.comp (continuous_fst.prodMk
    (hv.comp (continuous_snd.prodMk (continuous_fst.inv.smul (continuous_const (y := q))))))
  exact ht.congr (fun z => (coinducedCosetValues_action A S z.2 z.1 q).symm)

end
end Dubon2026
