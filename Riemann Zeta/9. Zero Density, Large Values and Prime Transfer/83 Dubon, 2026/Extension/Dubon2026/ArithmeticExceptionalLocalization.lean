import Dubon2026.ArithmeticExceptionalTraceDuality
import Dubon2026.ArithmeticGlobalCupOrthogonality

/-! # Actual global localization in the exceptional-place trace pairing

The proved support and global invariant sum identify the actual global
restriction images as orthogonal in one fixed, perfect local product.
This supplies the forward inclusion and dimension bound needed for DUB-17's
Poitou-Tate/Selmer step. The reverse arithmetic inclusion is not assumed or claimed.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped BigOperators NumberField

attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)

/-- The original global cyclotomic-twisted trace-zero H1. -/
abbrev RationalArithmeticTraceDualH1 :=
  ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
    (matrixTraceZeroCharacterAction_continuous σ hσ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)

/-- Simultaneous original trace-zero restriction at the actual exceptional primes. -/
def rationalArithmeticTraceH1Localization :
    ContinuousTraceZeroAdjointH1 σ hσ →ₗ[ZMod q]
      RationalArithmeticExceptionalTraceH1 a q ha σ hσ :=
  LinearMap.pi fun p =>
    show ContinuousTraceZeroAdjointH1 σ hσ →ₗ[ZMod q]
      rationalArithmeticPrimeTraceH1Module a q σ hσ p.val from
        continuousTraceZeroH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
          (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous

/-- Simultaneous original twisted restriction, including the proved cyclotomic action comparison. -/
def rationalArithmeticTraceDualH1Localization :
    RationalArithmeticTraceDualH1 a q hqa σ hσ →ₗ[ZMod q]
      RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ :=
  LinearMap.pi fun p =>
    show RationalArithmeticTraceDualH1 a q hqa σ hσ →ₗ[ZMod q]
      rationalArithmeticPrimeTraceDualH1Module a q σ hσ p.val from
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ

/-- The class-dependent support sum equals the sum over the fixed exceptional set.
Every omitted prime invariant is proved zero, rather than assumed to vanish. -/
theorem rationalArithmeticFiniteH2InvariantSum_eq_exceptionalSum
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha x =
      ∑ p : ↥(rationalArithmeticExceptionalPrimes a ha),
        rationalArithmeticPrimeH2Invariant a q hqa p.val.val p.val.property x := by
  classical
  rw [rationalArithmeticFiniteH2InvariantSum_apply,
    Finset.sum_coe_sort (rationalArithmeticExceptionalPrimes a ha)
      (fun p : Nat.Primes => rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x)]
  apply Finset.sum_subset
  · intro p hp
    by_contra hpa
    have hp' := Finsupp.mem_support_iff.mp hp
    apply hp'
    exact rationalArithmeticPrimeH2Invariant_eq_zero a q hqa p.val p.property ha
      (by simpa only [mem_rationalArithmeticExceptionalPrimes] using hpa) x
  · intro p _ hp
    exact Finsupp.notMem_support_iff.mp hp

/-- Each original restricted trace cup has the coherent invariant of the global cup. -/
theorem rationalArithmeticPrimeTraceH1ScalarCup_localization
    (p : ℕ) (hp : p.Prime)
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ)
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticPrimeTraceH1ScalarCup a q hqa p hp
      (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
      (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
      (continuousTraceZeroH1Restriction σ hσ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous y) =
      rationalArithmeticPrimeH2Invariant a q hqa p hp
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y) := by
  exact (congrArg (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp)
    (rationalArithmeticTraceZeroH1Cup_prime_restriction a q hqa σ hσ p hp x y)).symm

/-- The fixed local pairing of the actual restriction maps is the original global cup invariant sum. -/
theorem rationalArithmeticExceptionalTracePairing_localization
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ)
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
      (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x)
      (rationalArithmeticTraceH1Localization a q ha σ hσ y) =
        rationalArithmeticFiniteH2InvariantSum a q hqa ha
          (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y) := by
  apply (rationalArithmeticExceptionalTracePairing_apply a q hqa ha σ hσ _ _).trans
  apply Eq.trans _ (rationalArithmeticFiniteH2InvariantSum_eq_exceptionalSum
    a q hqa ha (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)).symm
  apply Finset.sum_congr rfl
  intro p _
  exact rationalArithmeticPrimeTraceH1ScalarCup_localization a q hqa σ hσ
    p.val.val p.val.property x y

/-- Actual global classes are orthogonal in the fixed exceptional-place pairing at every odd prime. -/
theorem rationalArithmeticExceptionalTracePairing_global_eq_zero
    (hq2 : q ≠ 2) (x : RationalArithmeticTraceDualH1 a q hqa σ hσ)
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
      (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x)
      (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0 := by
  letI : TopologicalSpace (rationalArithmeticRootRepresentation a q) := ⊥
  letI : DiscreteTopology (rationalArithmeticRootRepresentation a q) := ⟨rfl⟩
  letI : TopologicalSpace (rationalArithmeticUnitRepresentation a) := ⊥
  letI : DiscreteTopology (rationalArithmeticUnitRepresentation a) := ⟨rfl⟩
  rw [rationalArithmeticExceptionalTracePairing_localization]
  exact rationalArithmeticTraceZeroH1Cup_finiteInvariantSum_eq_zero a q hqa σ hσ ha hq2 x y

/-- The actual dual localization image, transported by the coherent pairing,
is contained in the annihilator of the primal localization image. -/
theorem rationalArithmeticTraceDualLocalization_range_le_annihilator (hq2 : q ≠ 2) :
    LinearMap.range ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
      (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) ≤
        (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)).dualAnnihilator := by
  rintro _ ⟨x, rfl⟩
  apply (Submodule.mem_dualAnnihilator _).mpr
  rintro _ ⟨y, rfl⟩
  exact rationalArithmeticExceptionalTracePairing_global_eq_zero a q hqa ha σ hσ hq2 x y

/-- The two genuine global images cannot together exceed the exceptional local dimension.
This is the inequality from reciprocity and local duality; it does not assert global exactness. -/
theorem rationalArithmeticTraceLocalization_finrank_add_le
    (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    Module.finrank (ZMod q) (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)) +
      Module.finrank (ZMod q)
        (LinearMap.range (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) ≤
      Module.finrank (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) := by
  haveI := rationalArithmeticExceptionalTraceH1_finite a q ha σ hσ
  haveI : Module.Finite (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
    Module.Finite.of_finite
  let P := rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
  haveI : P.IsPerfPair := rationalArithmeticExceptionalTracePairing_isPerfPair a q hqa ha σ hσ hn
  have hd := LinearEquiv.finrank_map_eq P.toPerfPair
    (LinearMap.range (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ))
  have hle := Submodule.finrank_mono
    (rationalArithmeticTraceDualLocalization_range_le_annihilator a q hqa ha σ hσ hq2)
  rw [LinearMap.range_comp] at hle
  change Module.finrank (ZMod q)
    ((LinearMap.range (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)).map
      P.toPerfPair.toLinearMap) ≤ _ at hle
  rw [hd] at hle
  exact (Nat.add_le_add_left hle _).trans_eq
    (Subspace.finrank_add_finrank_dualAnnihilator_eq
      (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)))

/-- The actual local obstruction map evaluates against all restricted global dual classes. -/
def rationalArithmeticTraceH1GlobalObstruction :
    RationalArithmeticExceptionalTraceH1 a q ha σ hσ →ₗ[ZMod q]
      Module.Dual (ZMod q) (RationalArithmeticTraceDualH1 a q hqa σ hσ) :=
  (rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).flip.compl₂
    (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)

/-- Global localization lands in the kernel of the genuine global-dual obstruction map.
Equality with this kernel is the remaining arithmetic exactness obligation. -/
theorem rationalArithmeticTraceH1Localization_range_le_obstruction_ker (hq2 : q ≠ 2) :
    LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ≤
      LinearMap.ker (rationalArithmeticTraceH1GlobalObstruction a q hqa ha σ hσ) := by
  rintro _ ⟨y, rfl⟩
  apply LinearMap.ext
  intro x
  exact rationalArithmeticExceptionalTracePairing_global_eq_zero a q hqa ha σ hσ hq2 x y

end
end Dubon2026
