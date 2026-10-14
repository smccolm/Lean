import Dubon2026.RationalPrimeChangedCyclotomicClosureFrobenius

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 800000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction wittCyclotomicRootDVR
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

theorem rationalPrimeChangedCyclotomicClosure_baseChangeFrobenius_root
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
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
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha]
      𝒪[rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha]] :
    let K := rationalPrimeLocalField p hp
    let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
    let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
    let algebraLM : Algebra L M := j.toRingHom.toAlgebra
    letI : SMul L M := algebraLM.toSMul
    letI : Algebra L M := algebraLM
    letI : IsScalarTower K L M := IsScalarTower.of_algHom j
    galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M)
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
      (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
  let algebraLM : Algebra L M := j.toRingHom.toAlgebra
  letI : SMul L M := algebraLM.toSMul
  letI : Algebra L M := algebraLM
  letI : IsScalarTower K L M := IsScalarTower.of_algHom j
  let ζL := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  let ζM := rationalPrimeChangedCyclotomicClosureRoot p hp n a u hu ha
  apply j.injective
  calc
    j (galoisBaseChangeRestriction K E L M
        (localFieldArithmeticFrobenius E M) ζL) =
        localFieldArithmeticFrobenius E M (j ζL) :=
      galoisBaseChangeRestriction_commutes K E L M _ ζL
    _ = localFieldArithmeticFrobenius E M ζM := by
      rw [rationalPrimeOriginalCyclotomicClosureRoot_inclusion]
    _ = ζM ^ b :=
      rationalPrimeChangedCyclotomicClosureFrobenius_root
        p hp n a b u hu ha hcoprimeA hcoprimeB hab
    _ = (j ζL) ^ b := by
      rw [rationalPrimeOriginalCyclotomicClosureRoot_inclusion]
    _ = j (ζL ^ b) := (map_pow j ζL b).symm

/-- The normed changed uniformizer has the required inverse-unit action on
the actual prime-power root under normalized finite local reciprocity. -/
theorem rationalPrimeChangedCyclotomicClosure_reciprocity_norm_uniformizer_root
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
    ∃ θE : 𝒪[E], ∃ hθE : Irreducible θE,
      ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
        Algebra.norm K (-algebraMap 𝒪[E] E θE) = (a : K) * p ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (Units.map (Algebra.norm K (S := E))
            (Units.mk0 (-algebraMap 𝒪[E] E θE)
              (by intro h; exact hθE.ne_zero (Subtype.ext (neg_eq_zero.mp h))))))).toMul
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
  obtain ⟨θE, hθE, hunramified, hnorm, hreciprocity⟩ :=
    rationalPrimeChangedCyclotomicClosure_reciprocity_norm_uniformizer
      p hp hp2 n a u hu ha
  letI : Algebra.FormallyUnramified 𝒪[E] 𝒪[M] := hunramified
  refine ⟨θE, hθE, hunramified, hnorm, ?_⟩
  rw [hreciprocity]
  exact rationalPrimeChangedCyclotomicClosure_baseChangeFrobenius_root
    p hp n a b u hu ha hcoprimeA hcoprimeB hab

end
end Dubon2026
