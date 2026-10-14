import Dubon2026.RationalPrimeOriginalCyclotomicNorm
import Dubon2026.RationalPrimeChangedCyclotomicClosureNaturalAction

/-! # The actual natural-unit action on the closure cyclotomic root

The same-stage norm `N(ζ - 1) = p` makes the rational prime trivial under
finite cyclic reciprocity.  Multiplicativity then cancels the prime factor
from the already proved `(a * p)` changed-uniformizer action.  The resulting
theorem identifies the normalized reciprocity action of the literal natural
unit `a` with the inverse exponent on the actual prime-power root.  This is
the natural-unit local formula required by DUB-17 before rational-unit and
global principal-product assembly.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 1200000

/-- The literal nonzero natural unit in the original rational local field. -/
def rationalPrimeNaturalUnit (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    (rationalPrimeLocalField p hp)ˣ :=
  Units.mk0 (a : rationalPrimeLocalField p hp) (by
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact ha (dvd_zero p)
    have h := (algebraMap ℚ (rationalPrimeLocalField p hp)).injective.ne
      (Nat.cast_ne_zero.mpr ha0 : (a : ℚ) ≠ 0)
    simpa only [map_natCast, map_zero] using h)

/-- The explicit natural unit has literal field value `a`. -/
@[simp] theorem rationalPrimeNaturalUnit_val
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    (rationalPrimeNaturalUnit p hp a ha : rationalPrimeLocalField p hp) = a := rfl

/-- The explicit natural and prime units multiply to the already used
natural-times-prime unit. -/
theorem rationalPrimeNaturalUnit_mul_prime
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    rationalPrimeNaturalUnit p hp a ha * rationalPrimePrimeUnit p hp =
      rationalPrimeNaturalMulPrimeUnit p hp a ha := by
  apply Units.ext
  rfl

/-- On the exact closure stage, reciprocity of `a * p` equals reciprocity of
`a` because the prime factor is an actual same-stage norm. -/
theorem rationalPrimeOriginalCyclotomicClosure_reciprocity_mul_prime_eq_natural
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ) (ha : ¬p ∣ a)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    letI : IsCyclic Gal(L/K) :=
      rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha))).toMul =
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  have hpzero : (ρ (Additive.ofMul (rationalPrimePrimeUnit p hp))).toMul = 1 :=
    by simpa only [ρ] using
      rationalPrimeOriginalCyclotomicClosure_reciprocity_prime p hp hp2 n a u hu ha
  have hpzero' : ρ (Additive.ofMul (rationalPrimePrimeUnit p hp)) = 0 := by
    simpa using congrArg Multiplicative.toAdd hpzero
  have hadd : ρ (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha)) =
      ρ (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha)) := by
    rw [← rationalPrimeNaturalUnit_mul_prime p hp a ha]
    change ρ (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha) +
        Additive.ofMul (rationalPrimePrimeUnit p hp)) =
      ρ (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))
    rw [map_add, hpzero', add_zero]
  exact congrArg Additive.toMul hadd

/-- The literal natural unit acts on the actual closure prime-power root by
the inverse exponent under normalized finite cyclic reciprocity. -/
theorem rationalPrimeChangedCyclotomicClosure_reciprocity_natural_root
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))] :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
    let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
    let algebraLM : Algebra L M := j.toRingHom.toAlgebra
    letI : SMul L M := algebraLM.toSMul
    letI : Algebra L M := algebraLM
    letI : IsScalarTower K L M := IsScalarTower.of_algHom j
    letI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsCyclic Gal(L/K) :=
      rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) := ⟨rfl⟩
    ∃ θE : 𝒪[E], Irreducible θE ∧
      ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
        Algebra.norm K (-algebraMap 𝒪[E] E θE) = (a : K) * p ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul
            (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
  let algebraLM : Algebra L M := j.toRingHom.toAlgebra
  letI : SMul L M := algebraLM.toSMul
  letI : Algebra L M := algebraLM
  letI : IsScalarTower K L M := IsScalarTower.of_algHom j
  letI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) := ⟨rfl⟩
  obtain ⟨θE, hθE, hunramified, hnorm, haction⟩ :=
    rationalPrimeChangedCyclotomicClosure_reciprocity_norm_uniformizer_root
      p hp hp2 n a b u hu ha hcoprimeA hcoprimeB hab
  letI : Algebra.FormallyUnramified 𝒪[E] 𝒪[M] := hunramified
  refine ⟨θE, hθE, hunramified, hnorm, ?_⟩
  have hunit : Units.map (Algebra.norm K (S := E))
        (Units.mk0 (-algebraMap 𝒪[E] E θE)
          (by intro h; exact hθE.ne_zero (Subtype.ext (neg_eq_zero.mp h)))) =
      rationalPrimeNaturalMulPrimeUnit p hp a ha := by
    apply Units.ext
    exact hnorm
  have hapAction :
      (localFieldFiniteCyclicReciprocity K Ω L
        (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha))).toMul
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
    rw [← hunit]
    exact haction
  have hrecip :=
    rationalPrimeOriginalCyclotomicClosure_reciprocity_mul_prime_eq_natural
      p hp hp2 n a ha u hu
  rw [hrecip] at hapAction
  exact hapAction


/-- Every positive natural unit away from an odd rational prime supplies every
closure-stage witness and acts literally on the actual prime-power root by the
inverse exponent under normalized local reciprocity. -/
theorem rationalPrimeNaturalUnitChangedCyclotomicClosure_reciprocity_root
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b : ℕ,
      a.Coprime (q ^ (n + 1)) ∧ b.Coprime (q ^ (n + 1)) ∧
      a * b ≡ 1 [MOD q ^ (n + 1)] ∧
      let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
      let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
      ∃ (_ : FiniteDimensional K E) (_ : ValuativeRel E)
        (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E))
        (_ : ValuativeRel M) (_ : TopologicalSpace M)
        (_ : IsNonarchimedeanLocalField M)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M))
        (_ : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)),
        let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
        let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
        let algebraLM : Algebra L M := j.toRingHom.toAlgebra
        letI : SMul L M := algebraLM.toSMul
        letI : Algebra L M := algebraLM
        letI : IsScalarTower K L M := IsScalarTower.of_algHom j
        letI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsCyclic Gal(L/K) :=
          rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) := ⟨rfl⟩
        ∃ θE : 𝒪[E], Irreducible θE ∧
          ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
            Algebra.norm K (-algebraMap 𝒪[E] E θE) = (a : K) * p ∧
            (localFieldFiniteCyclicReciprocity K Ω L
              (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul
                (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
              (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  dsimp only
  obtain ⟨u, hu, _⟩ := rationalPrimeNaturalWittNorm_exists p hp n a ha
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb, hab⟩ := primePowerNaturalUnit_exists_inverse p n a ha
  have hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)) := by
    simpa only [rationalPrimePlace_natGenerator] using hp.coprime_pow_of_not_dvd ha
  have hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)) := by
    simpa only [rationalPrimePlace_natGenerator] using hb
  have hab' : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)] := by
    simpa only [rationalPrimePlace_natGenerator] using hab
  refine ⟨u, hu, b, hcoprimeA, hcoprimeB, hab', ?_⟩
  obtain ⟨fdE, valE, topE, localE, extKE, valM, topM, localM, extKM, extEM, _⟩ :=
    rationalPrimeChangedCyclotomicClosure_exists_local_structure p hp n a u hu ha
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  letI : FiniteDimensional K E := fdE
  letI : ValuativeRel E := valE
  letI : TopologicalSpace E := topE
  letI : IsNonarchimedeanLocalField E := localE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) := extKE
  letI : ValuativeRel M := valM
  letI : TopologicalSpace M := topM
  letI : IsNonarchimedeanLocalField M := localM
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) := extKM
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) := extEM
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact rationalPrimeChangedCyclotomicClosure_reciprocity_natural_root
    p hp hp2 n a b u hu ha hcoprimeA hcoprimeB hab'

end
end Dubon2026
