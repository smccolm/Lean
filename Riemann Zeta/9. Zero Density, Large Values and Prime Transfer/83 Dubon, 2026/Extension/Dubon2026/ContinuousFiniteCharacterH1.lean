import Dubon2026.ContinuousRootCharacterCup

/-! # Actual finite characters represent every original trivial H1 class

This supplies the exact character represented by the corestriction of a
cyclotomic-stage character. The original cocycle function is unchanged.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- An original continuous trivial one-cocycle is its actual continuous finite
character, using the pinned cocycle identities on the same function. -/
def continuousGaloisFiniteCharacterOfCocycle
    (c : continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))) :
    Gal(Ω/K) →ₜ* Multiplicative (ZMod n) where
  toFun g := Multiplicative.ofAdd (c.val g)
  map_one' := congrArg Multiplicative.ofAdd (groupCohomology.cocycles₁_map_one c.val)
  map_mul' g h := by
    change c.val (g * h) = c.val g + c.val h
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h
    change c.val (g * h) = c.val h + c.val g at hc
    exact hc.trans (add_comm _ _)
  continuous_toFun := c.property

/-- Recovering the finite character retains exactly the original continuous
trivial one-cocycle, including its values and continuity proof. -/
theorem continuousGaloisFiniteCharacterOfCocycle_cocycle
    (c : continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))) :
    continuousGaloisFiniteCharacterOneCocycle n
      (continuousGaloisFiniteCharacterOfCocycle n c) = c := rfl

/-- Every original continuous H1 class of the trivial finite module has an
actual continuous-character representative, with no assumed dimension formula. -/
theorem continuousGaloisFiniteCharacterH1_surjective
    (x : ContinuousRepresentationH1
      (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) continuous_snd) :
    ∃ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle n χ) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => exact ⟨continuousGaloisFiniteCharacterOfCocycle n c, rfl⟩

end
end Dubon2026
