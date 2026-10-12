import Dubon2026.CoinducedHomogeneousCocycles

/-! # Continuity of original coinduced homogeneous values

Actual coefficient evaluation is continuous because it is identity evaluation
after the already proved original coinduced action. This proves continuity of
the explicit H2 prism witness needed for DUB-17's continuous Shapiro comparison.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]

include hA hS in
/-- Evaluation of the original coinduced function is jointly continuous in
its original group argument and its actual coefficient. -/
theorem coinducedFunctionEvaluation_continuous :
    Continuous (fun z : G × Rep.coind S.subtype (Rep.res S.subtype A) => z.2.val z.1) := by
  have he : Continuous (fun f : Rep.coind S.subtype (Rep.res S.subtype A) => f.val 1) :=
    continuous_of_discreteTopology
  have ht := he.comp (finiteCoinducedCoefficientAction_continuous A S hA hS)
  exact ht.congr (fun z => by
    change z.2.val (1 * z.1) = z.2.val z.1
    rw [one_mul])

include hA hS in
/-- Actual homogeneous triangle values are continuous along continuous original
vertices, including the subgroup-coordinate vertices of the prism witness. -/
theorem coinducedHomogeneousTwo_continuous {X : Type} [TopologicalSpace X]
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (hc : Continuous c)
    (x y z : X → G) (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun t => coinducedHomogeneousTwo A S c (x t) (y t) (z t)) :=
  (coinducedFunctionEvaluation_continuous A hA S hS).comp
    (hx.prodMk (hc.comp ((hx.inv.mul hy).prodMk (hy.inv.mul hz))))

end
end Dubon2026
