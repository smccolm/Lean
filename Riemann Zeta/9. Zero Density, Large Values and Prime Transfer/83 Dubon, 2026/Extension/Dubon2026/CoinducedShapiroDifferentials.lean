import Dubon2026.CoinducedShapiroCochains

/-! # Original Shapiro cochains preserve the low-degree differentials

The identities are proved in the genuine coinduced coefficients by the existing
termwise coset formulas. They supply the quotient compatibility required for
continuous Shapiro comparison in DUB-17's local duality dependency.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The actual degree-zero differential is preserved by the original lift. -/
theorem coinducedShapiroOne_coboundary (a : A) :
    coinducedShapiroOne A S (groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype) a) =
      groupCohomology.d₀₁ (Rep.coind S.subtype (Rep.res S.subtype A)) (coinducedShapiroZero A S a) := by
  funext g
  apply coinducedCosetValues_injective A S
  change coinducedCosetValues A S (coinducedShapiroOne A S _ g) =
    coinducedCosetValues A S
      ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (coinducedShapiroZero A S a) -
        coinducedShapiroZero A S a)
  rw [map_sub, coinducedShapiroOne_values]
  funext q
  change cosetTraceOneTerm A S _ g (g⁻¹ • q) =
    coinducedCosetValues A S
      ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (coinducedShapiroZero A S a)) q -
      coinducedCosetValues A S (coinducedShapiroZero A S a) q
  rw [coinducedCosetValues_action, coinducedShapiroZero_values]
  change A.ρ (g • g⁻¹ • q).out
      (A.ρ (cosetTransition S g (g⁻¹ • q)) a - a) =
        A.ρ g (A.ρ (g⁻¹ • q).out a) - A.ρ q.out a
  rw [map_sub, cosetTransition_action, smul_inv_smul]

/-- The actual degree-one differential commutes with the original coinduced
lift, by the existing termwise differential identity at the exact translated coset. -/
theorem coinducedShapiroTwo_differential (f : S → A) :
    coinducedShapiroTwo A S (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) =
      groupCohomology.d₁₂ (Rep.coind S.subtype (Rep.res S.subtype A)) (coinducedShapiroOne A S f) := by
  funext gh
  rcases gh with ⟨g, h⟩
  apply coinducedCosetValues_injective A S
  change coinducedCosetValues A S (coinducedShapiroTwo A S _ (g, h)) =
    coinducedCosetValues A S
      ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (coinducedShapiroOne A S f h) -
        coinducedShapiroOne A S f (g * h) + coinducedShapiroOne A S f g)
  rw [map_add, map_sub, coinducedShapiroTwo_values]
  funext q
  change cosetTraceTwoTerm A S _ g h ((g * h)⁻¹ • q) =
    coinducedCosetValues A S
      ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (coinducedShapiroOne A S f h)) q -
      coinducedCosetValues A S (coinducedShapiroOne A S f (g * h)) q +
      coinducedCosetValues A S (coinducedShapiroOne A S f g) q
  rw [coinducedCosetValues_action, coinducedShapiroOne_values,
    coinducedShapiroOne_values, coinducedShapiroOne_values]
  simpa only [mul_inv_rev, mul_smul, smul_inv_smul] using
    cosetTraceTwoTerm_differential A S f g h ((g * h)⁻¹ • q)

/-- The original degree-one lift sends every genuine subgroup cocycle to an
actual coinduced cocycle, because the same original differential vanishes. -/
theorem coinducedShapiroOne_mem_cocycles
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    coinducedShapiroOne A S c ∈
      groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A)) := by
  change groupCohomology.d₁₂ (Rep.coind S.subtype (Rep.res S.subtype A))
    (coinducedShapiroOne A S c) = 0
  rw [← coinducedShapiroTwo_differential]
  have hc : groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) c = 0 := c.property
  rw [hc, map_zero]

/-- The same degree-two lift preserves the actual original cocycle equation,
term by term in the genuine coinduced coefficient action. -/
theorem coinducedShapiroTwo_mem_cocycles
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    coinducedShapiroTwo A S c ∈
      groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)) := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  apply coinducedCosetValues_injective A S
  rw [map_add, map_add]
  funext q
  change coinducedCosetValues A S (coinducedShapiroTwo A S c (g * h, k)) q +
      coinducedCosetValues A S (coinducedShapiroTwo A S c (g, h)) q =
    coinducedCosetValues A S
      ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (coinducedShapiroTwo A S c (h, k))) q +
      coinducedCosetValues A S (coinducedShapiroTwo A S c (g, h * k)) q
  rw [coinducedCosetValues_action, coinducedShapiroTwo_values,
    coinducedShapiroTwo_values, coinducedShapiroTwo_values, coinducedShapiroTwo_values]
  simpa only [mul_inv_rev, mul_smul, smul_inv_smul] using
    cosetTraceTwoTerm_cocycle A S c g h k (((g * h) * k)⁻¹ • q)

end
end Dubon2026
