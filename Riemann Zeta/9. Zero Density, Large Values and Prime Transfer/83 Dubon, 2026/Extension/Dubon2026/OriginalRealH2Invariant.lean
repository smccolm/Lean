import Dubon2026.OriginalRealComplexPeriodSign
import Dubon2026.CyclicCharacterInvariantPairing

/-! # The original real unit-H2 invariant and its actual character pairing

The original real period-sign equivalence fixes the nontrivial invariant
to one half in the rational circle. The native cyclic character-pairing
theorem evaluates every actual real carry at the sign-selected complex
conjugation. This supplies the local real invariant needed for DUB-17's
finite-plus-real principal carry comparison.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

/-- Minus one generates the actual integral unit group. -/
private theorem integerSign_generates : ∀ u : ℤˣ, u ∈ Subgroup.zpowers (-1 : ℤˣ) := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact (Subgroup.zpowers (-1 : ℤˣ)).one_mem
  · exact Subgroup.mem_zpowers _

/-- The two actual signs are indexed by zero and one modulo two. -/
def originalIntegerSignIndex : Additive ℤˣ ≃+ ZMod 2 :=
  (zmodAddEquivOfGenerator (G := Additive ℤˣ) integerSign_generates
    (by rw [Nat.card_congr Additive.toMul, Nat.card_eq_fintype_card, Fintype.card_units_int])).symm

/-- The negative sign has exactly index one. -/
theorem originalIntegerSignIndex_neg_one :
    originalIntegerSignIndex (Additive.ofMul (-1 : ℤˣ)) = 1 := by
  exact zmodAddEquivOfGenerator_symm_apply_generator _ _

/-- The index of the original real sign is zero for positive units and one
for negative units, using the actual nonzero real value. -/
theorem originalIntegerSignIndex_realSign (u : ℝˣ) :
    originalIntegerSignIndex (Additive.ofMul (originalRealUnitsSign u)) =
      if 0 < u.val then 0 else 1 := by
  by_cases hu : 0 < u.val
  · rw [(originalRealUnitsSign_eq_one_iff u).mpr hu, if_pos hu]
    exact map_zero originalIntegerSignIndex
  · have hs : originalRealUnitsSign u = -1 :=
      (Int.units_eq_one_or (originalRealUnitsSign u)).resolve_left
        (fun h => hu ((originalRealUnitsSign_eq_one_iff u).mp h))
    rw [hs, if_neg hu, originalIntegerSignIndex_neg_one]

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

attribute [local instance] originalRealPeriodQuadratic

/-- The actual real unit-H2 invariant: the nontrivial period sign maps to
one half in the original rational circle. -/
def originalRealUnitH2Invariant :
    GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) →+ AddCircle (1 : ℚ) :=
  (rationalCyclicInvariant 2).comp
    (originalIntegerSignIndex.toAddMonoidHom.comp
      originalRealComplexH2SignEquiv.toAddEquiv.toAddMonoidHom)

/-- The real unit-H2 invariant detects the actual original cohomology class. -/
theorem originalRealUnitH2Invariant_injective : Function.Injective originalRealUnitH2Invariant :=
  (rationalCyclicInvariant_injective 2).comp
    (originalIntegerSignIndex.injective.comp originalRealComplexH2SignEquiv.injective)

/-- Every actual real finite-character carry has invariant equal to its
character evaluated at sign-selected actual complex conjugation. -/
theorem originalRealUnitH2Invariant_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(ℂ/ℝ) →* Multiplicative (ZMod n)) (u : ℝˣ) :
    originalRealUnitH2Invariant
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
      rationalCyclicInvariant n (χ (if 0 < u.val then 1 else Complex.conjAe)).toAdd := by
  let j := originalIntegerSignIndex (Additive.ofMul (originalRealUnitsSign u))
  have hc : Nat.card Gal(ℂ/ℝ) = 2 :=
    (orderOf_eq_card_of_forall_mem_zpowers originalRealComplexConjugation_generates).symm.trans
      originalRealComplexConjugation_order
  have hval : zmodMulEquivOfGenerator originalRealComplexConjugation_generates hc
      (Multiplicative.ofAdd j) = (if 0 < u.val then 1 else Complex.conjAe) := by
    dsimp only [j]
    rw [originalIntegerSignIndex_realSign]
    split_ifs
    · exact map_one _
    · exact zmodMulEquivOfGenerator_apply_ofAdd_one _ _
  have hpair := cyclicCharacter_rationalInvariant_pairing Complex.conjAe
    originalRealComplexConjugation_generates hc χ j
  rw [hval, originalRealComplexConjugation_order] at hpair
  change rationalCyclicInvariant 2 (originalIntegerSignIndex
    (originalRealComplexH2SignEquiv
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)))) = _
  rw [originalRealComplexH2SignEquiv_characterCarry, map_nsmul, map_nsmul]
  exact hpair.symm

end
end Dubon2026
