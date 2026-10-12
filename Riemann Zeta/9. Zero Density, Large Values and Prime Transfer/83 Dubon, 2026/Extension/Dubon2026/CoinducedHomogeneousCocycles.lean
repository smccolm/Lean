import Dubon2026.ContinuousCoinducedEvaluation
import Dubon2026.CoinducedSubgroupCoordinates

/-! # Actual homogeneous values of original coinduced cocycles

These are explicit evaluations of the original inhomogeneous cocycles, not a
new cohomology theory. Their literal identities supply the two Shapiro inverse
homotopies required for DUB-17's continuous local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The original degree-one cocycle evaluated on an actual homogeneous edge. -/
def coinducedHomogeneousOne
    (c : G → Rep.coind S.subtype (Rep.res S.subtype A)) (x y : G) : A :=
  (c (x⁻¹ * y)).val x

/-- The original degree-two cocycle evaluated on an actual homogeneous triangle. -/
def coinducedHomogeneousTwo
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (x y z : G) : A :=
  (c (x⁻¹ * y, y⁻¹ * z)).val x

/-- The original one-cocycle equation is exactly the homogeneous edge identity. -/
theorem coinducedHomogeneousOne_cocycle
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y z : G) :
    coinducedHomogeneousOne A S c x z =
      coinducedHomogeneousOne A S c y z + coinducedHomogeneousOne A S c x y := by
  have hc := congrArg (fun f : Rep.coind S.subtype (Rep.res S.subtype A) => f.val x)
    ((groupCohomology.mem_cocycles₁_iff _).mp c.property (x⁻¹ * y) (y⁻¹ * z))
  change (c ((x⁻¹ * y) * (y⁻¹ * z))).val x =
    (c (y⁻¹ * z)).val (x * (x⁻¹ * y)) + (c (x⁻¹ * y)).val x at hc
  simpa only [coinducedHomogeneousOne, mul_assoc, mul_inv_cancel_left] using hc

/-- The original two-cocycle equation is exactly the homogeneous tetrahedron identity. -/
theorem coinducedHomogeneousTwo_cocycle
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y z t : G) :
    coinducedHomogeneousTwo A S c x z t + coinducedHomogeneousTwo A S c x y z =
      coinducedHomogeneousTwo A S c y z t + coinducedHomogeneousTwo A S c x y t := by
  have hc := congrArg (fun f : Rep.coind S.subtype (Rep.res S.subtype A) => f.val x)
    ((groupCohomology.mem_cocycles₂_iff _).mp c.property (x⁻¹ * y) (y⁻¹ * z) (z⁻¹ * t))
  change (c ((x⁻¹ * y) * (y⁻¹ * z), z⁻¹ * t)).val x + (c (x⁻¹ * y, y⁻¹ * z)).val x =
    (c (y⁻¹ * z, z⁻¹ * t)).val (x * (x⁻¹ * y)) + (c (x⁻¹ * y, (y⁻¹ * z) * (z⁻¹ * t))).val x at hc
  simpa only [coinducedHomogeneousTwo, mul_assoc, mul_inv_cancel_left] using hc

/-- Actual left subgroup translation preserves homogeneous degree-one values
with precisely the original coefficient action. -/
theorem coinducedHomogeneousOne_equivariant
    (c : G → Rep.coind S.subtype (Rep.res S.subtype A)) (s : S) (x y : G) :
    coinducedHomogeneousOne A S c ((s : G) * x) ((s : G) * y) =
      A.ρ (s : G) (coinducedHomogeneousOne A S c x y) := by
  have hxy : ((s : G) * x)⁻¹ * ((s : G) * y) = x⁻¹ * y := by group
  change (c (((s : G) * x)⁻¹ * ((s : G) * y))).val ((s : G) * x) = _
  rw [hxy]
  exact (c (x⁻¹ * y)).property s x

/-- Actual homogeneous degree-two values have the same original subgroup equivariance. -/
theorem coinducedHomogeneousTwo_equivariant
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (s : S) (x y z : G) :
    coinducedHomogeneousTwo A S c ((s : G) * x) ((s : G) * y) ((s : G) * z) =
      A.ρ (s : G) (coinducedHomogeneousTwo A S c x y z) := by
  have hxy : ((s : G) * x)⁻¹ * ((s : G) * y) = x⁻¹ * y := by group
  have hyz : ((s : G) * y)⁻¹ * ((s : G) * z) = y⁻¹ * z := by group
  change (c ((((s : G) * x)⁻¹ * ((s : G) * y)),
    (((s : G) * y)⁻¹ * ((s : G) * z)))).val ((s : G) * x) = _
  rw [hxy, hyz]
  exact (c (x⁻¹ * y, y⁻¹ * z)).property s x

end
end Dubon2026
