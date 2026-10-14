import Dubon2026.RationalPrimeChangedCyclotomicClosureReciprocityAction
import Dubon2026.RationalPrimeNaturalWittNorm

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 1200000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction wittCyclotomicRootDVR
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

/-- The explicit nonzero base-field unit `a * p` attached to a natural unit
away from the rational prime `p`. -/
def rationalPrimeNaturalMulPrimeUnit
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    (rationalPrimeLocalField p hp)ˣ :=
  Units.mk0 ((a : rationalPrimeLocalField p hp) * p) (by
    apply mul_ne_zero
    · have ha0 : a ≠ 0 := by
        intro h
        subst a
        exact ha (dvd_zero p)
      have h := (algebraMap ℚ (rationalPrimeLocalField p hp)).injective.ne
        (Nat.cast_ne_zero.mpr ha0 : (a : ℚ) ≠ 0)
      simpa only [map_natCast, map_zero] using h
    · have h := (algebraMap ℚ (rationalPrimeLocalField p hp)).injective.ne
        (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)
      simpa only [map_natCast, map_zero] using h)

/-- The explicit natural-times-prime unit has its literal field value. -/
@[simp] theorem rationalPrimeNaturalMulPrimeUnit_val
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    (rationalPrimeNaturalMulPrimeUnit p hp a ha : rationalPrimeLocalField p hp) =
      (a : rationalPrimeLocalField p hp) * p := rfl

/-- Every positive natural unit away from an odd rational prime supplies all
closure-stage witnesses, and its normed changed uniformizer acts on the actual
prime-power root by the inverse exponent under normalized local reciprocity. -/
theorem rationalPrimeNaturalChangedCyclotomicClosure_reciprocity_root
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
              (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha))).toMul
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
  obtain ⟨θE, hθE, hunramified, hnorm, haction⟩ :=
    rationalPrimeChangedCyclotomicClosure_reciprocity_norm_uniformizer_root
      p hp hp2 n a b u hu ha hcoprimeA hcoprimeB hab'
  letI : Algebra.FormallyUnramified 𝒪[E] 𝒪[M] := hunramified
  refine ⟨θE, hθE, hunramified, hnorm, ?_⟩
  have hunit : Units.map (Algebra.norm K (S := E))
        (Units.mk0 (-algebraMap 𝒪[E] E θE)
          (by intro h; exact hθE.ne_zero (Subtype.ext (neg_eq_zero.mp h)))) =
      rationalPrimeNaturalMulPrimeUnit p hp a ha := by
    apply Units.ext
    exact hnorm
  rw [← hunit]
  exact haction

end
end Dubon2026
