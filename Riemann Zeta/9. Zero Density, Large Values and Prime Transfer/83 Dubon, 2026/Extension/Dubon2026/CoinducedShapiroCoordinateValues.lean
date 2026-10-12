import Dubon2026.CoinducedHomogeneousPrism

/-! # Exact coordinate values of the original Shapiro composites

The original coset transition equals the change in the actual subgroup
coordinate. Consequently the Shapiro/evaluation composites are the precise
vertex changes in the proved homogeneous identities. This connects those
identities to the actual maps required by DUB-17's local duality argument.
-/

namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] (S : Subgroup G)

/-- The actual coset transition is exactly the change in original subgroup coordinates. -/
theorem coinducedSubgroupCoordinate_transition (g t : G) :
    cosetTransition S g (g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S)) =
      (coinducedSubgroupCoordinate S t)⁻¹ * coinducedSubgroupCoordinate S (t * g) := by
  have hq : g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S) = QuotientGroup.mk (t * g)⁻¹ := by
    rw [mul_inv_rev]
    rfl
  apply Subtype.ext
  change (g • g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S)).out⁻¹ *
      (g * (g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S)).out) =
    (coinducedSubgroupCoordinate S t : G)⁻¹ * (coinducedSubgroupCoordinate S (t * g) : G)
  rw [smul_inv_smul, hq, coinducedSubgroupCoordinate_val, coinducedSubgroupCoordinate_val]
  change _ = (t * (QuotientGroup.mk t⁻¹ : G ⧸ S).out)⁻¹ *
    ((t * g) * (QuotientGroup.mk (t * g)⁻¹ : G ⧸ S).out)
  group

variable {R : Type} [CommRing R] (A : Rep.{0} R G)

/-- The original degree-one Shapiro lift has the literal subgroup-coordinate value. -/
theorem coinducedShapiroOne_apply (f : S → A) (g t : G) :
    (coinducedShapiroOne A S f g).val t =
      A.ρ (coinducedSubgroupCoordinate S t : G)
        (f ((coinducedSubgroupCoordinate S t)⁻¹ * coinducedSubgroupCoordinate S (t * g))) := by
  change A.ρ t (A.ρ (g • g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S)).out
    (f (cosetTransition S g (g⁻¹ • (QuotientGroup.mk t⁻¹ : G ⧸ S))))) = _
  rw [smul_inv_smul, ← Module.End.mul_apply, ← map_mul,
    coinducedSubgroupCoordinate_transition, coinducedSubgroupCoordinate_val]
  rfl

/-- The original degree-two lift retains both exact subgroup-coordinate changes. -/
theorem coinducedShapiroTwo_apply (c : S × S → A) (g h t : G) :
    (coinducedShapiroTwo A S c (g, h)).val t =
      A.ρ (coinducedSubgroupCoordinate S t : G)
        (c ((coinducedSubgroupCoordinate S t)⁻¹ * coinducedSubgroupCoordinate S (t * g),
          (coinducedSubgroupCoordinate S (t * g))⁻¹ *
            coinducedSubgroupCoordinate S ((t * g) * h))) := by
  let q : G ⧸ S := QuotientGroup.mk t⁻¹
  have hq : g⁻¹ • q = QuotientGroup.mk (t * g)⁻¹ := by
    rw [mul_inv_rev]
    rfl
  have h₁ : h • ((g * h)⁻¹ • q) = g⁻¹ • q := by
    simp only [mul_inv_rev, mul_smul, smul_inv_smul]
  have h₂ : (g * h)⁻¹ • q = h⁻¹ • (QuotientGroup.mk (t * g)⁻¹ : G ⧸ S) := by
    rw [mul_inv_rev, mul_smul, hq]
  change A.ρ t (A.ρ (g • h • (g * h)⁻¹ • q).out
    (c (cosetTransition S g (h • (g * h)⁻¹ • q), cosetTransition S h ((g * h)⁻¹ • q)))) = _
  rw [h₁, smul_inv_smul, coinducedSubgroupCoordinate_transition,
    h₂, coinducedSubgroupCoordinate_transition, ← Module.End.mul_apply, ← map_mul,
    coinducedSubgroupCoordinate_val]
  rfl

/-- The actual degree-one Shapiro/evaluation composite is the same original
homogeneous edge evaluated at the actual subgroup-coordinate vertices. -/
theorem coinducedShapiroOne_evaluation_value
    (c : G → Rep.coind S.subtype (Rep.res S.subtype A)) (g t : G) :
    (coinducedShapiroOne A S (fun s : S => (c (s : G)).val 1) g).val t =
      coinducedHomogeneousOne A S c (coinducedSubgroupCoordinate S t)
        (coinducedSubgroupCoordinate S (t * g)) := by
  rw [coinducedShapiroOne_apply]
  have he := (c ((coinducedSubgroupCoordinate S t : G)⁻¹ *
      (coinducedSubgroupCoordinate S (t * g) : G))).property
    (coinducedSubgroupCoordinate S t) 1
  simpa only [coinducedHomogeneousOne, Subgroup.coe_mul, Subgroup.coe_inv, mul_one] using he.symm

/-- The actual degree-two Shapiro/evaluation composite is the original
homogeneous triangle at the same actual subgroup-coordinate vertices. -/
theorem coinducedShapiroTwo_evaluation_value
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (g h t : G) :
    (coinducedShapiroTwo A S (fun z : S × S => (c (z.1, z.2)).val 1) (g, h)).val t =
      coinducedHomogeneousTwo A S c (coinducedSubgroupCoordinate S t)
        (coinducedSubgroupCoordinate S (t * g)) (coinducedSubgroupCoordinate S ((t * g) * h)) := by
  rw [coinducedShapiroTwo_apply]
  have he := (c ((coinducedSubgroupCoordinate S t : G)⁻¹ *
        (coinducedSubgroupCoordinate S (t * g) : G),
      (coinducedSubgroupCoordinate S (t * g) : G)⁻¹ *
        (coinducedSubgroupCoordinate S ((t * g) * h) : G))).property
    (coinducedSubgroupCoordinate S t) 1
  simpa only [coinducedHomogeneousTwo, Subgroup.coe_mul, Subgroup.coe_inv, mul_one] using he.symm

end
end Dubon2026
