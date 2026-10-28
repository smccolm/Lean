import Dubon2026.SourceGammaOneHeckeFiberPresentation

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> geometric fiber multiplicities.
The proved generic intersection-orbit criterion gives the actual generic fiber
bijection and its exact weighted order sum. All-point injectivity remains open. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceCurve
open scoped MatrixGroups StabilizerCharacter GammaOne

theorem toFiber_injective_of_generic (M d : ℕ) [NeZero M] [NeZero d] (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ)
    (hc : Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2) :
    Function.Injective (toFiber M d hT τ) := by
  intro q₁ q₂ he
  have he' : analyticPlace hT (rep M d τ q₁) = analyticPlace hT (rep M d τ q₂) :=
    congrArg Subtype.val he
  obtain ⟨γ, hγ⟩ := (analyticHeckePlace_eq_iff_orbit_of_generic M d hT _ _
    ((card_stabilizer_rep M d τ q₁).trans hc)).mp he'
  have hrel : (MulAction.orbitRel (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) (MulAction.orbit SL(2, ℤ) τ))
      q₂.out q₁.out := by
    show q₂.out ∈ MulAction.orbit (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) q₁.out
    refine MulAction.mem_orbit_iff.mpr ⟨⟨γ, le_plusMinus _ γ.2⟩, ?_⟩
    exact Subtype.ext hγ
  calc q₁ = Quotient.mk _ q₁.out := (Quotient.out_eq q₁).symm
    _ = Quotient.mk _ q₂.out := (Quotient.sound hrel).symm
    _ = q₂ := Quotient.out_eq q₂

/-- The proved bijection between analytic orbit classes and the actual finite fiber. -/
def equivOfGeneric (M d : ℕ) [NeZero M] [NeZero d] (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ)
    (hc : Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2) :
    OrbitQuot M d τ ≃ Fiber M d τ :=
  Equiv.ofBijective (toFiber M d hT τ) ⟨toFiber_injective_of_generic M d hT τ hc, toFiber_surjective M d hT τ⟩

theorem sum_orders_of_generic (M d : ℕ) [NeZero M] [NeZero d] (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ)
    (hc : Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2)
    [Fintype (OrbitQuot M d τ)] :
    (∑ q : OrbitQuot M d τ, (analyticPlace hT (rep M d τ q)).ord
      (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ))) =
      ∑ᶠ P : Fiber M d τ, P.1.ord (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ)) := by
  letI : Finite (Fiber M d τ) := Finite.of_equiv (OrbitQuot M d τ) (equivOfGeneric M d hT τ hc)
  letI : Fintype (Fiber M d τ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact Fintype.sum_equiv (equivOfGeneric M d hT τ hc) _ _ (fun _ => rfl)

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
