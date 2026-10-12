import Dubon2026.CoinducedShapiroCoordinateValues
import Dubon2026.ContinuousCoinducedHomogeneousValues

/-! # The original degree-two Shapiro prism

The explicit two-triangle prism is a cochain in the original coinduced
representation. Its differential gives the actual Shapiro/evaluation
comparison required by DUB-17's finite-module local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The original coinduced one-cochain given by the two-triangle prism. -/
def coinducedShapiroTwoHomotopy
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (g : G) :
    Rep.coind S.subtype (Rep.res S.subtype A) :=
  ⟨fun t =>
    coinducedHomogeneousTwo A S c t (coinducedSubgroupCoordinate S t)
      (coinducedSubgroupCoordinate S (t * g)) -
    coinducedHomogeneousTwo A S c t (t * g) (coinducedSubgroupCoordinate S (t * g)), by
    intro s t
    change coinducedHomogeneousTwo A S c ((s : G) * t)
        (coinducedSubgroupCoordinate S ((s : G) * t))
        (coinducedSubgroupCoordinate S (((s : G) * t) * g)) -
      coinducedHomogeneousTwo A S c ((s : G) * t) (((s : G) * t) * g)
        (coinducedSubgroupCoordinate S (((s : G) * t) * g)) = _
    rw [mul_assoc, coinducedSubgroupCoordinate_mul, coinducedSubgroupCoordinate_mul]
    change coinducedHomogeneousTwo A S c ((s : G) * t)
        ((s : G) * (coinducedSubgroupCoordinate S t : G))
        ((s : G) * (coinducedSubgroupCoordinate S (t * g) : G)) -
      coinducedHomogeneousTwo A S c ((s : G) * t) ((s : G) * (t * g))
        ((s : G) * (coinducedSubgroupCoordinate S (t * g) : G)) = _
    rw [coinducedHomogeneousTwo_equivariant, coinducedHomogeneousTwo_equivariant, map_sub]
    rfl⟩

/-- The original lifted evaluation differs from the original two-cocycle by
the differential of the actual coinduced prism cochain. -/
theorem coinducedShapiroTwo_evaluation_sub
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A))) :
    coinducedShapiroTwo A S (fun z : S × S => (c (z.1, z.2)).val 1) - c.val =
      groupCohomology.d₁₂ (Rep.coind S.subtype (Rep.res S.subtype A))
        (coinducedShapiroTwoHomotopy A S c) := by
  funext z
  rcases z with ⟨g, h⟩
  apply Subtype.ext
  funext t
  change (coinducedShapiroTwo A S (fun z : S × S => (c (z.1, z.2)).val 1) (g, h)).val t -
      (c (g, h)).val t =
    (coinducedShapiroTwoHomotopy A S c h).val (t * g) -
      (coinducedShapiroTwoHomotopy A S c (g * h)).val t +
      (coinducedShapiroTwoHomotopy A S c g).val t
  rw [coinducedShapiroTwo_evaluation_value]
  have hc := coinducedHomogeneousTwo_prism A S c t (t * g) ((t * g) * h)
    (coinducedSubgroupCoordinate S t) (coinducedSubgroupCoordinate S (t * g))
    (coinducedSubgroupCoordinate S ((t * g) * h))
  have ho : coinducedHomogeneousTwo A S c t (t * g) ((t * g) * h) =
      (c (g, h)).val t := by
    simp only [coinducedHomogeneousTwo, inv_mul_cancel_left]
  rw [ho] at hc
  simpa only [coinducedShapiroTwoHomotopy, mul_assoc] using hc.symm

end
end Dubon2026
