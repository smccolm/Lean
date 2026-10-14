import Dubon2026.RationalPrimeChangedIntegralRoot
import Dubon2026.RationalPrimeChangedAuxiliaryField
import Mathlib.RingTheory.Localization.Integral

/-! # The changed integral root algebra inside the actual auxiliary field

The literal changed Eisenstein polynomial maps to the already identified
minimal polynomial of the actual auxiliary generator.  Its root algebra
therefore maps into that field.  The DVR structure makes the map injective:
a nonzero prime kernel would be the unique maximal ideal and would kill the
uniformizing root, contradicting the proved nonzero norm.  This is the
integral comparison required before DUB-17's spectral local-field transport.
-/
namespace Dubon2026
noncomputable section
open Polynomial IsLocalRing
open scoped ValuativeRel

attribute [local instance] rationalPrimeChangedIntegralRootDomain
  rationalPrimeChangedIntegralRootDVR rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction

/-- Use the literal composite integer action through the original completion. -/
local instance rationalPrimeChangedAuxiliaryIntegerAlgebra
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    Algebra 𝒪[rationalPrimeLocalField p hp]
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
  ((algebraMap (rationalPrimeLocalField p hp)
    (rationalPrimeChangedAuxiliaryField p hp n u)).comp
      (algebraMap 𝒪[rationalPrimeLocalField p hp]
        (rationalPrimeLocalField p hp))).toAlgebra

/-- The explicit integer action is the scalar composite used by evaluation. -/
local instance rationalPrimeChangedAuxiliaryIntegerTower
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    IsScalarTower 𝒪[rationalPrimeLocalField p hp] (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The literal integral changed polynomial becomes the known minimal
polynomial after passage to the original rational-prime completion. -/
theorem rationalPrimeChangedIntegralPolynomial_map_original
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    (rationalPrimeChangedIntegralPolynomial p hp n u).map
      (algebraMap 𝒪[rationalPrimeLocalField p hp] (rationalPrimeLocalField p hp)) =
      primeChangedPrimitivePolynomial p
        ((a : rationalPrimeLocalField p hp) * p) n := by
  rw [rationalPrimeChangedIntegralPolynomial, primeChangedPrimitivePolynomial_map]
  apply congrArg (fun π => primeChangedPrimitivePolynomial p π n)
  rw [map_mul, hu, map_natCast, map_natCast]

/-- The actual auxiliary generator satisfies the literal integral changed polynomial. -/
theorem rationalPrimeChangedAuxiliaryPoint_integral_aeval
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    aeval (rationalPrimeChangedAuxiliaryPoint p hp n u)
      (rationalPrimeChangedIntegralPolynomial p hp n u) = 0 := by
  rw [← Polynomial.aeval_map_algebraMap (A := rationalPrimeLocalField p hp),
    rationalPrimeChangedIntegralPolynomial_map_original p hp n a u hu]
  have hmin : minpoly (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryPoint p hp n u) =
      primeChangedPrimitivePolynomial p
        ((a : rationalPrimeLocalField p hp) * p) n := by
    simpa only [rationalPrimePlace_natGenerator] using
      (rationalPrimeChangedAuxiliaryPoint_minpoly p hp n a u hu ha)
  rw [← hmin]
  exact minpoly.aeval _ _

/-- The literal changed integral root algebra maps to the genuine auxiliary field. -/
def rationalPrimeChangedIntegralRootAlgHom
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u) →ₐ[
      𝒪[rationalPrimeLocalField p hp]] rationalPrimeChangedAuxiliaryField p hp n u :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (rationalPrimeChangedAuxiliaryPoint p hp n u)
    (rationalPrimeChangedAuxiliaryPoint_integral_aeval p hp n a u hu ha)

/-- The comparison map sends the literal adjoined root to the actual auxiliary generator. -/
theorem rationalPrimeChangedIntegralRootAlgHom_root
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
      (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u)) =
      rationalPrimeChangedAuxiliaryPoint p hp n u :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The actual auxiliary generator is nonzero, derived from its exact field norm. -/
theorem rationalPrimeChangedAuxiliaryPoint_ne_zero
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeChangedAuxiliaryPoint p hp n u ≠ 0 := by
  letI : FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
    (rationalPrimeChangedAuxiliaryField_finrank_and_finite p hp n a u hu ha).2
  intro hzero
  have hnorm := rationalPrimeChangedAuxiliaryPoint_norm_neg p hp n a u hu ha
  rw [hzero, neg_zero, Algebra.norm_zero] at hnorm
  have hcasta : (a : rationalPrimeLocalField p hp) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hu]
    exact Subtype.ext h
  have hcastp : (p : rationalPrimeLocalField p hp) ≠ 0 := by
    intro h
    apply (rationalPrimeValuationInteger_irreducible_prime p hp).ne_zero
    exact Subtype.ext h
  exact (mul_ne_zero hcasta hcastp) hnorm.symm

/-- The literal integral comparison is injective; no model-equivalence
certificate is assumed. -/
theorem rationalPrimeChangedIntegralRootAlgHom_injective
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    Function.Injective (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha) := by
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let φ := rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  have hmax : (RingHom.ker φ.toRingHom).IsMaximal :=
    (RingHom.ker_isPrime φ.toRingHom).isMaximal hker
  have heq : RingHom.ker φ.toRingHom = maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal hmax
  have huniformizer : maximalIdeal (AdjoinRoot f) = Ideal.span {AdjoinRoot.root f} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (AdjoinRoot.root f)).mp
      (rationalPrimeChangedIntegralRoot_irreducible p hp n u)
  have hroot : AdjoinRoot.root f ∈ RingHom.ker φ.toRingHom := by
    rw [heq, huniformizer]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hz : φ (AdjoinRoot.root f) = 0 := hroot
  rw [rationalPrimeChangedIntegralRootAlgHom_root] at hz
  exact rationalPrimeChangedAuxiliaryPoint_ne_zero p hp n a u hu ha hz

/-- Clearing coefficient denominators realizes every evaluated fraction-field
polynomial as a quotient in its monic root algebra. -/
theorem adjoinRoot_eval_eq_div_of_fractionRing
    {O K E : Type*} [CommRing O] [IsDomain O] [Field K] [Field E]
    [Algebra O K] [IsFractionRing O K] [Algebra K E] [Algebra O E]
    [IsScalarTower O K E] (f : O[X])
    (φ : AdjoinRoot f →ₐ[O] E) (θ : E)
    (hθ : φ (AdjoinRoot.root f) = θ) (hroot : aeval θ f = 0)
    (g : K[X]) :
    ∃ x y : AdjoinRoot f, aeval θ g = φ x / φ y := by
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors O) g
  let G := IsLocalization.integerNormalization (nonZeroDivisors O) g
  refine ⟨AdjoinRoot.mk f G, algebraMap O (AdjoinRoot f) b, ?_⟩
  have hφ : φ = AdjoinRoot.liftAlgHom f (Algebra.ofId O E) θ hroot := by
    apply AdjoinRoot.algHom_ext
    rw [hθ, AdjoinRoot.liftAlgHom_root]
  rw [hφ, AdjoinRoot.liftAlgHom_mk, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]
  have heval : aeval θ G = algebraMap O E b * aeval θ g := by
    calc
      aeval θ G = aeval θ (Polynomial.map (algebraMap O K) G) := by
        rw [Polynomial.aeval_map_algebraMap]
      _ = aeval θ (b • g) := congrArg (fun q : K[X] => aeval θ q) hclear
      _ = algebraMap O E b * aeval θ g := by
        simp only [Algebra.smul_def, map_mul]
        rw [IsScalarTower.algebraMap_apply O K (K[X]),
          (aeval θ).commutes, IsScalarTower.algebraMap_apply O K E]
  have hbE : algebraMap O E b ≠ 0 := by
    have hbK : algebraMap O K b ≠ 0 :=
      IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K le_rfl hb
    rw [IsScalarTower.algebraMap_apply O K E]
    simpa using (algebraMap K E).injective.ne hbK
  change aeval θ g = aeval θ G / algebraMap O E b
  rw [heval]
  field_simp

/-- Every actual auxiliary-field element is a quotient from the literal
changed root algebra. -/
theorem rationalPrimeChangedIntegralRoot_div_surjective
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    letI : Algebra (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u))
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
        (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
    ∀ z : rationalPrimeChangedAuxiliaryField p hp n u,
      ∃ x y : AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u),
        z = algebraMap _ _ x / algebraMap _ _ y := by
  let O := 𝒪[rationalPrimeLocalField p hp]
  let K := rationalPrimeLocalField p hp
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let B := AdjoinRoot f
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let θ := rationalPrimeChangedAuxiliaryPoint p hp n u
  let φ := rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
  letI : Algebra B E := φ.toAlgebra
  haveI : IsScalarTower O K E := by infer_instance
  intro z
  let basis := IntermediateField.adjoin.powerBasis
    (rationalPrimeChangedFieldPoint_isIntegral p hp n a u hu ha)
  obtain ⟨g, _, rfl⟩ := basis.exists_eq_aeval' z
  exact adjoinRoot_eval_eq_div_of_fractionRing f φ θ
    (rationalPrimeChangedIntegralRootAlgHom_root p hp n a u hu ha)
    (rationalPrimeChangedAuxiliaryPoint_integral_aeval p hp n a u hu ha) g

/-- The actual auxiliary field is the genuine fraction field of the literal
changed DVR model. -/
theorem rationalPrimeChangedAuxiliaryField_isFractionRing
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    letI : Algebra (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u))
      (rationalPrimeChangedAuxiliaryField p hp n u) :=
        (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
    IsFractionRing (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u))
      (rationalPrimeChangedAuxiliaryField p hp n u) := by
  let B := AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u)
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  letI : Algebra B E :=
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
  haveI : FaithfulSMul B E :=
    (faithfulSMul_iff_algebraMap_injective B E).mpr
      (rationalPrimeChangedIntegralRootAlgHom_injective p hp n a u hu ha)
  apply IsFractionRing.of_field B E
  exact rationalPrimeChangedIntegralRoot_div_surjective p hp n a u hu ha

end
end Dubon2026
