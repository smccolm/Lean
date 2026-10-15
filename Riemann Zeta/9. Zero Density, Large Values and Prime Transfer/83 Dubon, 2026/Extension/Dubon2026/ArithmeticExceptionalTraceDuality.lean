import Dubon2026.ArithmeticCoherentLocalH1Duality
import Dubon2026.RationalPrimeTraceCupPerfect
import Dubon2026.RationalExceptionalPrimeFinite

/-! # The actual finite exceptional-place trace pairing

The Selmer localization sequence needs one fixed product of local H1 spaces,
not a support chosen separately for each cup class. We use the literal primes
dividing the exceptional integer and the already proved coherent local duality.
This establishes the ambient perfect pairing for DUB-17's global image comparison;
it does not assert the missing global image/annihilator equality.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped BigOperators NumberField

/-- The finite set of actual primes dividing the exceptional integer. -/
def rationalArithmeticExceptionalPrimes (a : 𝓞 ℚ) (ha : a ≠ 0) : Finset Nat.Primes :=
  (rationalExceptionalPrimeSet_finite a ha).toFinset

/-- Membership retains the original integer-ring divisibility condition. -/
@[simp] theorem mem_rationalArithmeticExceptionalPrimes
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : Nat.Primes) :
    p ∈ rationalArithmeticExceptionalPrimes a ha ↔ (p.val : 𝓞 ℚ) ∣ a :=
  Set.Finite.mem_toFinset _

/-- The actual local roots use the discrete coefficient topology. -/
local instance exceptionalTraceRootTopology (p : ℕ) (hp : p.Prime) (q : ℕ) :
    TopologicalSpace (galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q) := ⊥

/-- The chosen coefficient topology is discrete. -/
local instance exceptionalTraceRootDiscrete (p : ℕ) (hp : p.Prime) (q : ℕ) :
    DiscreteTopology (galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q) := ⟨rfl⟩

/-- The actual local algebraic units use the discrete coefficient topology. -/
local instance exceptionalTraceUnitTopology (p : ℕ) (hp : p.Prime) :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⊥

/-- The chosen unit coefficient topology is discrete. -/
local instance exceptionalTraceUnitDiscrete (p : ℕ) (hp : p.Prime) :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩

attribute [local instance] characterDualSequenceContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The original local trace cup, normalized using the same global root at every prime. -/
def rationalArithmeticPrimeTraceH1ScalarCup (p : ℕ) (hp : p.Prime)
    (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
      GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ) :=
  matrixTraceZeroNormalizedH1Cup ρ hρ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp)

/-- Actual local duality proves perfectness with the globally coherent normalization. -/
theorem rationalArithmeticPrimeTraceH1ScalarCup_isPerfPair (p : ℕ) (hp : p.Prime)
    (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
      GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalArithmeticPrimeTraceH1ScalarCup a q hqa p hp ρ hρ).IsPerfPair := by
  let χ := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
  letI : TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⟨rfl⟩
  haveI := rationalPrimeTraceZeroAdjointH1_finite p hp q ρ hρ
  haveI : Module.Finite (ZMod q) (ContinuousTraceZeroAdjointH1 ρ hρ) := Module.Finite.of_finite
  exact matrixTraceZeroNormalizedH1Cup_isPerfPair ρ hρ χ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp) hn
    (rationalArithmeticLocalH1ScalarCup_isPerfPair a q hqa p hp
      (matrixTraceZeroAdjointRep ρ) (matrixTraceZeroAdjointAction_continuous ρ hρ))

variable (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)

/-- The original trace-zero deformation H1, bundled with its existing module structure. -/
def rationalArithmeticPrimeTraceH1Module (p : Nat.Primes) : ModuleCat (ZMod q) :=
  ModuleCat.of (ZMod q) (ContinuousTraceZeroAdjointH1
    (σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
    (hσ.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous))

/-- The original twisted H1, bundled with its existing module structure. -/
def rationalArithmeticPrimeTraceDualH1Module (p : Nat.Primes) : ModuleCat (ZMod q) :=
  let j := rationalPrimeArithmeticRestriction a p.val p.property
  let χ := rationalPrimeCyclotomicCoefficientCharacter p.val p.property q (ZMod q)
  ModuleCat.of (ZMod q) (ContinuousRepresentationH1
    (matrixTraceZeroCharacterRep (σ.comp j.toMonoidHom) χ.toMonoidHom)
    (matrixTraceZeroCharacterAction_continuous (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
      χ.toMonoidHom χ.continuous))

/-- The actual product of local trace-zero deformation spaces at the exceptional primes. -/
abbrev RationalArithmeticExceptionalTraceH1 :=
  (p : ↥(rationalArithmeticExceptionalPrimes a ha)) →
    rationalArithmeticPrimeTraceH1Module a q σ hσ p.val

/-- Its cyclotomic-twisted trace-dual local product, with the original prime characters. -/
abbrev RationalArithmeticExceptionalTraceDualH1 :=
  (p : ↥(rationalArithmeticExceptionalPrimes a ha)) →
    rationalArithmeticPrimeTraceDualH1Module a q σ hσ p.val

/-- Sum the genuine coherent local trace pairings on the fixed exceptional-place product. -/
def rationalArithmeticExceptionalTracePairing :
    RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ →ₗ[ZMod q]
      RationalArithmeticExceptionalTraceH1 a q ha σ hσ →ₗ[ZMod q] ZMod q :=
  ∑ p : ↥(rationalArithmeticExceptionalPrimes a ha),
    (show rationalArithmeticPrimeTraceDualH1Module a q σ hσ p.val →ₗ[ZMod q]
      rationalArithmeticPrimeTraceH1Module a q σ hσ p.val →ₗ[ZMod q] ZMod q from
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)).compl₁₂
        (LinearMap.proj p) (LinearMap.proj p)

/-- Evaluation is exactly the finite sum of the original coherent local cup coordinates. -/
theorem rationalArithmeticExceptionalTracePairing_apply
    (x : RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ)
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x y =
      ∑ p : ↥(rationalArithmeticExceptionalPrimes a ha),
        rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
          (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
          (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
          (x p) (y p) := by
  simp only [rationalArithmeticExceptionalTracePairing, LinearMap.sum_apply,
    LinearMap.compl₁₂_apply, LinearMap.proj_apply]
  rfl

/-- The fixed exceptional product is finite by the proved finiteness at each actual local field. -/
theorem rationalArithmeticExceptionalTraceH1_finite :
    Finite (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) := by
  letI (p : ↥(rationalArithmeticExceptionalPrimes a ha)) :
      Finite (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :=
    rationalPrimeTraceZeroAdjointH1_finite p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
  exact Pi.finite

/-- The fixed twisted exceptional product is finite by the original local coefficient theorem. -/
theorem rationalArithmeticExceptionalTraceDualH1_finite :
    Finite (RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ) := by
  letI (p : ↥(rationalArithmeticExceptionalPrimes a ha)) :
      Finite (rationalArithmeticPrimeTraceDualH1Module a q σ hσ p.val) :=
    rationalPrimeCyclotomicTraceZeroH1_finite p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
  exact Pi.finite

private theorem exceptionalTracePairing_single_right
    (x : RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ)
    (p : ↥(rationalArithmeticExceptionalPrimes a ha))
    (y : rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x (Pi.single p y) =
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        (x p) y := by
  let B (r : ↥(rationalArithmeticExceptionalPrimes a ha)) :
      rationalArithmeticPrimeTraceDualH1Module a q σ hσ r.val →ₗ[ZMod q]
        rationalArithmeticPrimeTraceH1Module a q σ hσ r.val →ₗ[ZMod q] ZMod q :=
    rationalArithmeticPrimeTraceH1ScalarCup a q hqa r.val.val r.val.property
      (σ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).continuous)
  change (∑ r, (B r).compl₁₂ (LinearMap.proj r) (LinearMap.proj r)) x (Pi.single p y) = B p (x p) y
  simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro r _ hr
    rw [Pi.single_eq_of_ne hr]
    exact map_zero _
  · simp

private theorem exceptionalTracePairing_single_left
    (p : ↥(rationalArithmeticExceptionalPrimes a ha))
    (x : rationalArithmeticPrimeTraceDualH1Module a q σ hσ p.val)
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ (Pi.single p x) y =
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        x (y p) := by
  let B (r : ↥(rationalArithmeticExceptionalPrimes a ha)) :
      rationalArithmeticPrimeTraceDualH1Module a q σ hσ r.val →ₗ[ZMod q]
        rationalArithmeticPrimeTraceH1Module a q σ hσ r.val →ₗ[ZMod q] ZMod q :=
    rationalArithmeticPrimeTraceH1ScalarCup a q hqa r.val.val r.val.property
      (σ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).continuous)
  change (∑ r, (B r).compl₁₂ (LinearMap.proj r) (LinearMap.proj r)) (Pi.single p x) y = B p x (y p)
  simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro r _ hr
    rw [Pi.single_eq_of_ne hr]
    exact DFunLike.congr_fun (map_zero _) _
  · simp

/-- The fixed exceptional-place trace pairing is perfect on its actual local H1 products.
The matrix dimension condition is the original trace-duality condition. -/
theorem rationalArithmeticExceptionalTracePairing_isPerfPair
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).IsPerfPair := by
  haveI := rationalArithmeticExceptionalTraceH1_finite a q ha σ hσ
  haveI : Module.Finite (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
    Module.Finite.of_finite
  apply LinearMap.IsPerfPair.of_injective'
  · intro x z hx
    funext p
    apply (rationalArithmeticPrimeTraceH1ScalarCup_isPerfPair a q hqa p.val.val p.val.property
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
      hn).bijective_left.injective
    apply LinearMap.ext
    intro y
    have h := DFunLike.congr_fun hx (Pi.single p y)
    simpa only [exceptionalTracePairing_single_right] using h
  · intro x z hx
    funext p
    apply (rationalArithmeticPrimeTraceH1ScalarCup_isPerfPair a q hqa p.val.val p.val.property
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
      hn).bijective_right.injective
    apply LinearMap.ext
    intro y
    have h := DFunLike.congr_fun hx (Pi.single p y)
    simpa only [LinearMap.flip_apply, exceptionalTracePairing_single_left] using h

end
end Dubon2026
