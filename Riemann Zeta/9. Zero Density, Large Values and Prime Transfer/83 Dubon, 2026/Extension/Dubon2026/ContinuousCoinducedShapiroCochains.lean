import Dubon2026.CoinducedShapiroDifferentials

/-! # The actual coinduced Shapiro lifts preserve continuity

Open cosets, the existing continuous transition map and the original action
give continuous one- and two-cochain lifts into the same coinduced object.
This supplies the genuine continuous witnesses needed in DUB-17's local duality.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]

include hA hS in
/-- The actual degree-one Shapiro lift is continuous in the original coinduced
coefficient topology; the finite coset product supplies the continuous reconstruction. -/
theorem coinducedShapiroOne_continuous (f : S → A) (hf : Continuous f) :
    Continuous (coinducedShapiroOne A S f) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  have hr : Continuous (coinducedCosetReconstruct A S) := continuous_of_discreteTopology
  apply hr.comp
  apply continuous_pi
  intro q
  exact hA.comp
    ((hout.comp (continuous_id.smul (continuous_inv.smul continuous_const))).prodMk
      (hf.comp ((cosetTransition_continuous S hS).comp
        (continuous_id.prodMk (continuous_inv.smul (continuous_const (y := q)))))))

include hA hS in
/-- Jointly continuous original two-cochains lift to jointly continuous actual
coinduced two-cochains using the same two subgroup transition coordinates. -/
theorem coinducedShapiroTwo_continuous (c : S × S → A) (hc : Continuous c) :
    Continuous (coinducedShapiroTwo A S c) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  have hr : Continuous (coinducedCosetReconstruct A S) := continuous_of_discreteTopology
  apply hr.comp
  apply continuous_pi
  intro q
  have hq : Continuous (fun z : G × G => (z.1 * z.2)⁻¹ • q) :=
    (continuous_fst.mul continuous_snd).inv.smul continuous_const
  exact hA.comp
    ((hout.comp (continuous_fst.smul (continuous_snd.smul hq))).prodMk
      (hc.comp (((cosetTransition_continuous S hS).comp
        (continuous_fst.prodMk (continuous_snd.smul hq))).prodMk
        ((cosetTransition_continuous S hS).comp (continuous_snd.prodMk hq)))))

end
end Dubon2026
