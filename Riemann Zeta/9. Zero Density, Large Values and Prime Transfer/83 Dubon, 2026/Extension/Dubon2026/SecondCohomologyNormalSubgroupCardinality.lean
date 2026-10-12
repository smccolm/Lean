import Dubon2026.OriginalCoinducedGlobalDimensionShift
import Dubon2026.FiniteExactModuleDivisibility

/-! # Actual second cohomology orders through a normal subgroup -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- With zero original subgroup H1, actual H2 of the full group is finite
and its order divides the product of the two original normal-subgroup and
quotient-invariant H2 orders. The proof uses actual dimension shifts and the
pinned first-degree inflation-restriction exact sequence on the genuine quotient. -/
theorem secondCohomology_normal_subgroup_card_dvd
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
    [Finite (groupCohomology (A.quotientToInvariants S) 2)]
    [Finite (groupCohomology (Rep.res S.subtype A) 2)] :
    Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) ∣
        Nat.card (groupCohomology (A.quotientToInvariants S) 2) *
          Nat.card (groupCohomology (Rep.res S.subtype A) 2) := by
  let Q := originalCoinducedQuotient A
  let eG : groupCohomology Q 1 ≅ groupCohomology A 2 :=
    @asIso _ _ _ _ (groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl)
      (originalCoinducedGlobalDimensionShift_isIso A)
  let eS : groupCohomology (Rep.res S.subtype Q) 1 ≅
      groupCohomology (Rep.res S.subtype A) 2 :=
    @asIso _ _ _ _ (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl)
      (originalCoinducedDimensionShift_isIso A S)
  let eQ : groupCohomology (Q.quotientToInvariants S) 1 ≅
      groupCohomology (A.quotientToInvariants S) 2 :=
    @asIso _ _ _ _ (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl)
      (originalCoinducedInvariantDimensionShift_isIso A S hfirst)
  let X := groupCohomology.H1InfRes Q S
  haveI : Finite X.X₁ := Finite.of_equiv _ eQ.symm.toLinearEquiv.toEquiv
  haveI : Finite X.X₃ := Finite.of_equiv _ eS.symm.toLinearEquiv.toEquiv
  have hm : Mono X.f := inferInstance
  obtain ⟨hfinite, hcard⟩ := finite_exact_three_module_card_dvd
    (A := X.X₁) (B := X.X₂) (C := X.X₃) X.f.hom X.g.hom
      ((ModuleCat.mono_iff_injective _).mp hm)
      (groupCohomology.H1InfRes_exact Q S).moduleCat_range_eq_ker
  haveI : Finite X.X₂ := hfinite
  refine ⟨Finite.of_equiv X.X₂ eG.toLinearEquiv.toEquiv, ?_⟩
  have hG : Nat.card X.X₂ = Nat.card (groupCohomology A 2) := Nat.card_congr eG.toLinearEquiv.toEquiv
  have hQ : Nat.card X.X₁ = Nat.card (groupCohomology (A.quotientToInvariants S) 2) :=
    Nat.card_congr eQ.toLinearEquiv.toEquiv
  have hS : Nat.card X.X₃ = Nat.card (groupCohomology (Rep.res S.subtype A) 2) :=
    Nat.card_congr eS.toLinearEquiv.toEquiv
  rwa [hG, hQ, hS] at hcard

end
end Dubon2026
