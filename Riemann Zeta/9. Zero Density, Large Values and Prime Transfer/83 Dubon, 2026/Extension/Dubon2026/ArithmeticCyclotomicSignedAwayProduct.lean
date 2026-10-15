import Dubon2026.ArithmeticCyclotomicReciprocityAwayConductor
import Dubon2026.ArithmeticCyclotomicRealSignAction
import Dubon2026.RationalPrimeNormalizedResidual

/-! # The real and away-prime cyclotomic product on one actual stage

Every away-prime reciprocity value is restricted to the same actual rational
Galois group.  This module multiplies those values there, computes the power
character of the finite product, and then adjoins the actual real-sign
automorphism.  Thus the remaining principal-product problem is reduced to
identifying one explicit unit of `ZMod n` with the forward ramified exponent.
-/
namespace Dubon2026
noncomputable section

open Polynomial IsCyclotomicExtension
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- Cyclotomic Galois groups are commutative because the canonical power
character is injective into the commutative unit group of `ZMod n`. -/
@[reducible] def rationalCyclotomicGalCommGroup
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] : CommGroup Gal(F/ℚ) := by
  let χ := IsCyclotomicExtension.autEquivPow F
    (cyclotomic.irreducible_rat (NeZero.pos n))
  let base : Group Gal(F/ℚ) := inferInstance
  exact
    { base with
      mul_comm := fun σ τ => by
        apply χ.injective
        simpa only [map_mul] using (mul_comm (χ σ) (χ τ)) }

/-- The actual away-prime reciprocity value, restricted to one fixed global
cyclotomic stage.  The canonical discrete structures are installed inside
the definition, so finite products do not carry a family of topology
parameters. -/
def arithmeticCyclotomicAwayAut
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (v : HeightOneSpectrum ℤ) (q : ℚˣ) : Gal(F/ℚ) := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let hp := Rat.HeightOneSpectrum.prime_natGenerator v
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a F p hp
  exact rationalArithmeticFiniteLocalRestriction a F p hp
    (localFieldFiniteCyclicReciprocity K Ω M
      (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul

/-- The power character of one packaged away-prime value is the existing
arithmetic Frobenius character. -/
theorem arithmeticCyclotomicAwayAut_autToPow
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (v : HeightOneSpectrum ℤ)
    (hvn : ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (q : ℚˣ) :
    hζ.autToPow ℚ (arithmeticCyclotomicAwayAut a F v q) =
      ZMod.unitOfCoprime (Rat.HeightOneSpectrum.natGenerator v)
          ((Rat.HeightOneSpectrum.prime_natGenerator v).coprime_iff_not_dvd.mpr hvn) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))
          (Additive.ofMul
            (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v) q)) := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let hp := Rat.HeightOneSpectrum.prime_natGenerator v
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a F p hp
  change hζ.autToPow ℚ
      (rationalArithmeticFiniteLocalRestriction a F p hp
        (localFieldFiniteCyclicReciprocity K Ω M
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul) = _
  exact arithmeticCyclotomic_reciprocity_away_conductor
    a F p hp n hvn hζ (rationalPrimeRationalUnit p hp q)

/-- The product of all selected away-prime reciprocity values on the common
actual cyclotomic stage. -/
def arithmeticCyclotomicAwayProduct
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ)) (q : ℚˣ) : Gal(F/ℚ) := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  exact ∏ v ∈ S, arithmeticCyclotomicAwayAut a F v q

/-- The explicit residue-class unit represented by the selected away-prime
factors. -/
def arithmeticCyclotomicAwayProductUnit
    (n : ℕ) (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ n) (q : ℚˣ) :
    (ZMod n)ˣ :=
  S.attach.prod fun v =>
    ZMod.unitOfCoprime (Rat.HeightOneSpectrum.natGenerator v.1)
        ((Rat.HeightOneSpectrum.prime_natGenerator v.1).coprime_iff_not_dvd.mpr
          (hS v.1 v.2)) ^
      localFieldUnitOrder
        (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
          (Rat.HeightOneSpectrum.prime_natGenerator v.1))
        (Additive.ofMul
          (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
            (Rat.HeightOneSpectrum.prime_natGenerator v.1) q))

/-- Multiplying the individual away-prime formulas on the common stage
multiplies their exact power characters. -/
theorem arithmeticCyclotomicAwayProduct_autToPow
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (q : ℚˣ) :
    hζ.autToPow ℚ (arithmeticCyclotomicAwayProduct a F n S q) =
      arithmeticCyclotomicAwayProductUnit n S hS q := by
  classical
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  change hζ.autToPow ℚ (∏ v ∈ S, arithmeticCyclotomicAwayAut a F v q) =
    S.attach.prod fun v =>
      ZMod.unitOfCoprime (Rat.HeightOneSpectrum.natGenerator v.1)
          ((Rat.HeightOneSpectrum.prime_natGenerator v.1).coprime_iff_not_dvd.mpr
            (hS v.1 v.2)) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
            (Rat.HeightOneSpectrum.prime_natGenerator v.1))
          (Additive.ofMul
            (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
              (Rat.HeightOneSpectrum.prime_natGenerator v.1) q))
  rw [map_prod (hζ.autToPow ℚ)
    (fun v => arithmeticCyclotomicAwayAut a F v q) S]
  rw [← Finset.prod_attach S
    (fun v => hζ.autToPow ℚ (arithmeticCyclotomicAwayAut a F v q))]
  apply Finset.prod_congr rfl
  intro v _hv
  exact arithmeticCyclotomicAwayAut_autToPow a F n v.1 (hS v.1 v.2) hζ q

/-- The actual real factor and every selected away-prime factor, multiplied
inside one rational cyclotomic Galois group. -/
def arithmeticCyclotomicSignedAwayProduct
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ)) (q : ℚˣ) : Gal(F/ℚ) := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  exact rationalCyclotomicRealSignAut n F q *
    arithmeticCyclotomicAwayProduct a F n S q

/-- The explicit residue-class unit represented jointly by the real sign and
the selected away-prime factors. -/
def arithmeticCyclotomicSignedAwayProductUnit
    (n : ℕ) (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ n) (q : ℚˣ) :
    (ZMod n)ˣ :=
  rationalCyclotomicRealSignUnit n q *
    arithmeticCyclotomicAwayProductUnit n S hS q

/-- The signed away product has exactly the sign unit times the product of
the individual normalized Frobenius characters. -/
theorem arithmeticCyclotomicSignedAwayProduct_autToPow
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (q : ℚˣ) :
    hζ.autToPow ℚ (arithmeticCyclotomicSignedAwayProduct a F n S q) =
      arithmeticCyclotomicSignedAwayProductUnit n S hS q := by
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup n F
  rw [arithmeticCyclotomicSignedAwayProduct, map_mul,
    rationalCyclotomicRealSignAut_autToPow n F q hζ,
    arithmeticCyclotomicAwayProduct_autToPow a F n S hS hζ q]
  rfl

/-- The signed away product therefore acts on the actual primitive root by
the displayed combined residue-class exponent. -/
theorem arithmeticCyclotomicSignedAwayProduct_apply_root
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (q : ℚˣ) :
    arithmeticCyclotomicSignedAwayProduct a F n S q ζ =
      ζ ^ ((arithmeticCyclotomicSignedAwayProductUnit n S hS q : (ZMod n)ˣ) :
        ZMod n).val := by
  rw [← hζ.autToPow_spec ℚ,
    arithmeticCyclotomicSignedAwayProduct_autToPow a F n S hS hζ q]

/-- A finite support omitting the rational prime `p` is automatically away
from every positive power of the conductor prime. -/
theorem finiteSupport_away_primePower
    (p : ℕ) (hp : p.Prime) (k : ℕ) (S : Finset (HeightOneSpectrum ℤ))
    (hpS : rationalPrimePlace p hp ∉ S) :
    ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ p ^ k := by
  intro v hvS hvdvd
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p :=
    (Rat.HeightOneSpectrum.prime_natGenerator v).dvd_of_dvd_pow hvdvd
  have heq : Rat.HeightOneSpectrum.natGenerator v = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left
      (Rat.HeightOneSpectrum.prime_natGenerator v).ne_one
  have hplace : rationalPrimePlace p hp = v := by
    subst p
    exact rationalPrimePlace_of_natGenerator v
  rw [hplace] at hpS
  exact hpS hvS

/-- The exact normalized residual supplies a conductor-free support whose
real and away-prime reciprocity factors are already multiplied on one actual
prime-power cyclotomic stage. -/
theorem rationalPrimeNormalizedResidual_exists_signedAwayProduct_action
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) (q : ℚˣ) :
    let N := p ^ (m + 1)
    letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
    let r := rationalPrimeNormalizedResidual p hp q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ N,
        (∀ v ∉ S, v.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v) r))) = r.val ∧
        arithmeticCyclotomicSignedAwayProduct a F N S r ζ =
          ζ ^ ((arithmeticCyclotomicSignedAwayProductUnit N S hS r : (ZMod N)ˣ) :
            ZMod N).val := by
  dsimp only
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := rationalPrimeNormalizedResidual p hp q
  obtain ⟨S, hpS, houtside, hproduct⟩ :=
    rationalPrimeNormalizedResidual_exists_away_signed_prime_product p hp q
  let hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ p ^ (m + 1) :=
    finiteSupport_away_primePower p hp (m + 1) S hpS
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · exact houtside
  · exact hproduct
  · exact arithmeticCyclotomicSignedAwayProduct_apply_root
      a F (p ^ (m + 1)) S hS hζ r

end
end Dubon2026
