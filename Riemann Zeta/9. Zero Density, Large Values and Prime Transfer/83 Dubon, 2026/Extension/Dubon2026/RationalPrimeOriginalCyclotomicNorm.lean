import Dubon2026.RationalPrimeChangedCyclotomicClosureFrobenius
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # The rational prime is a norm from the actual cyclotomic closure stage

The proved Witt Eisenstein polynomial transports irreducibility of the
prime-power cyclotomic polynomial to the original rational local field.
Mathlib's cyclotomic norm formula then gives the exact same-stage witness
`N(ζ - 1) = p`.  The finite cyclic reciprocity kernel theorem consequently
makes the prime factor act trivially in the precise closure stage used by
the changed-uniformizer action.  This is the cancellation input required
to isolate the natural unit in DUB-17.
-/

namespace Dubon2026
noncomputable section

open Polynomial
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime rationalPrimeWittOriginalAlgebra
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

private def polynomialTranslateEquiv (K : Type*) [CommRing K] (a : K) :
    K[X] ≃+* K[X] where
  toFun f := f.comp (X + C a)
  invFun f := f.comp (X - C a)
  left_inv f := by
    change (f.comp (X + C a)).comp (X - C a) = f
    rw [comp_assoc]
    simp
  right_inv f := by
    change (f.comp (X - C a)).comp (X + C a) = f
    rw [comp_assoc]
    simp
  map_add' f g := by simp
  map_mul' f g := by simp

/-- Irreducibility of a translated polynomial implies irreducibility of the
original polynomial via the literal translation automorphism. -/
theorem rationalPrimePolynomial_irreducible_of_comp_X_add_C
    {K : Type*} [Field K] (f : K[X]) (a : K)
    (h : Irreducible (f.comp (X + C a))) : Irreducible f := by
  exact (MulEquiv.irreducible_iff (polynomialTranslateEquiv K a).toMulEquiv (x := f)).mp h

/-- The translated prime-power cyclotomic polynomial is irreducible over the
actual rational `p`-adic field. -/
theorem rationalPrimePowerShiftedCyclotomic_irreducible
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Irreducible (primePowerShiftedCyclotomic (rationalPrimeLocalField p hp) p n) := by
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let W := WittVector q (AlgebraicClosure (ZMod q))
  let F := rationalPrimeWittField p hp
  have hW : Irreducible (primePowerShiftedCyclotomic W q n) := by
    exact wittCyclotomicPolynomial_irreducible q n
  have hF : Irreducible
      ((primePowerShiftedCyclotomic W q n).map (algebraMap W F)) :=
    (primePowerShiftedCyclotomic_monic W q n).irreducible_iff_irreducible_map_fraction_map.mp hW
  have hF' : Irreducible (primePowerShiftedCyclotomic F q n) := by
    simpa [primePowerShiftedCyclotomic, Polynomial.map_comp] using hF
  apply Polynomial.Monic.irreducible_of_irreducible_map
    (algebraMap (rationalPrimeLocalField p hp) F)
    _ (primePowerShiftedCyclotomic_monic _ p n)
  simpa [primePowerShiftedCyclotomic, Polynomial.map_comp, q,
    rationalPrimePlace_natGenerator] using hF'

/-- The prime-power cyclotomic polynomial itself is irreducible over the
actual rational `p`-adic field. -/
theorem rationalPrimePowerCyclotomic_irreducible
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Irreducible (Polynomial.cyclotomic (p ^ (n + 1))
      (rationalPrimeLocalField p hp)) := by
  apply rationalPrimePolynomial_irreducible_of_comp_X_add_C _ 1
  exact rationalPrimePowerShiftedCyclotomic_irreducible p hp n

/-- The literal root in the original finite cyclotomic stage retains its
exact prime-power order. -/
theorem rationalPrimeOriginalCyclotomicStageRoot_isPrimitive
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    IsPrimitiveRoot (rationalPrimeOriginalCyclotomicStageRoot p hp n)
      (p ^ (n + 1)) := by
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let Ω := wittCyclotomicField q n
  let L := rationalPrimeOriginalCyclotomicStage p hp n
  have hroot : IsPrimitiveRoot
      (((rationalPrimeOriginalCyclotomicStageRoot p hp n : L) : Ω))
      (q ^ (n + 1)) := by
    exact rationalPrimeWittCyclotomicFieldPrimitiveRoot_isPrimitive p hp n
  have hstage : IsPrimitiveRoot (rationalPrimeOriginalCyclotomicStageRoot p hp n)
      (q ^ (n + 1)) :=
    hroot.of_map_of_injective (f := L.toIntermediateField.val)
      L.toIntermediateField.val.injective
  simpa only [q, rationalPrimePlace_natGenerator] using hstage

/-- The original finite stage is the genuine cyclotomic extension generated
by its literal prime-power root. -/
theorem rationalPrimeOriginalCyclotomicStage_isCyclotomic
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    IsCyclotomicExtension {p ^ (n + 1)} (rationalPrimeLocalField p hp)
      (rationalPrimeOriginalCyclotomicStage p hp n) := by
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let K := rationalPrimeLocalField p hp
  let Ω := wittCyclotomicField q n
  have hμ : IsPrimitiveRoot (rationalPrimeWittCyclotomicFieldPrimitiveRoot p hp n)
      (q ^ (n + 1)) :=
    rationalPrimeWittCyclotomicFieldPrimitiveRoot_isPrimitive p hp n
  have h := originalPrimitiveRootStage_isCyclotomic K Ω hμ
  simpa only [rationalPrimeOriginalCyclotomicStage, q,
    rationalPrimePlace_natGenerator] using h

/-- At an odd prime, the exact norm of the literal cyclotomic uniformizer is
the rational prime. -/
theorem rationalPrimeOriginalCyclotomicStageRoot_norm_sub_one
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    Algebra.norm (rationalPrimeLocalField p hp)
        (rationalPrimeOriginalCyclotomicStageRoot p hp n - 1) =
      (p : rationalPrimeLocalField p hp) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclotomicExtension {p ^ (n + 1)} (rationalPrimeLocalField p hp)
      (rationalPrimeOriginalCyclotomicStage p hp n) :=
    rationalPrimeOriginalCyclotomicStage_isCyclotomic p hp n
  exact (rationalPrimeOriginalCyclotomicStageRoot_isPrimitive p hp n).norm_sub_one_of_prime_ne_two
    (rationalPrimePowerCyclotomic_irreducible p hp n) hp2

/-- The exact norm `N(ζ - 1) = p` transports to the actual closure stage
chosen for the general changed unit. -/
theorem rationalPrimeOriginalCyclotomicClosureRoot_norm_sub_one
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    Algebra.norm (rationalPrimeLocalField p hp)
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha - 1) =
      (p : rationalPrimeLocalField p hp) := by
  let K := rationalPrimeLocalField p hp
  let L₀ := rationalPrimeOriginalCyclotomicStage p hp n
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let e : L₀ ≃ₐ[K] L :=
    rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
  calc
    Algebra.norm K
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha - 1) =
        Algebra.norm K (e (rationalPrimeOriginalCyclotomicStageRoot p hp n - 1)) := by
          congr 1
          simp only [e, rationalPrimeOriginalCyclotomicClosureRoot, map_sub, map_one]
    _ = Algebra.norm K (rationalPrimeOriginalCyclotomicStageRoot p hp n - 1) :=
      Algebra.norm_eq_of_algEquiv e _
    _ = (p : K) := rationalPrimeOriginalCyclotomicStageRoot_norm_sub_one p hp hp2 n

/-- The literal nonzero rational prime as a unit of the original local field. -/
def rationalPrimePrimeUnit (p : ℕ) (hp : p.Prime) :
    (rationalPrimeLocalField p hp)ˣ :=
  Units.mk0 (p : rationalPrimeLocalField p hp) (by
    have h := (algebraMap ℚ (rationalPrimeLocalField p hp)).injective.ne
      (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)
    simpa only [map_natCast, map_zero] using h)

/-- The explicit prime unit has literal field value `p`. -/
@[simp] theorem rationalPrimePrimeUnit_val (p : ℕ) (hp : p.Prime) :
    (rationalPrimePrimeUnit p hp : rationalPrimeLocalField p hp) = p := rfl

/-- The rational prime is an actual field-unit norm from the same closure
cyclotomic stage used for the changed-unit reciprocity action. -/
theorem rationalPrimeOriginalCyclotomicClosure_exists_prime_norm
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = rationalPrimePrimeUnit p hp := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  have hnorm : Algebra.norm K (ζ - 1) = (p : K) :=
    rationalPrimeOriginalCyclotomicClosureRoot_norm_sub_one p hp hp2 n a u hu ha
  have hne : ζ - 1 ≠ 0 := by
    intro hzero
    have hzero' : (0 : K) = p := by simpa only [hzero, Algebra.norm_zero] using hnorm
    have hpK : (p : K) ≠ 0 := by
      have h := (algebraMap ℚ K).injective.ne
        (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)
      simpa only [map_natCast, map_zero] using h
    exact hpK hzero'.symm
  refine ⟨Units.mk0 (ζ - 1) hne, ?_⟩
  apply Units.ext
  exact hnorm

/-- Normalized finite cyclic reciprocity sends the rational prime to the
identity on the exact same closure cyclotomic stage. -/
theorem rationalPrimeOriginalCyclotomicClosure_reciprocity_prime
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    letI : IsCyclic Gal(L/K) :=
      rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimePrimeUnit p hp))).toMul = 1 := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  have hzero : localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimePrimeUnit p hp)) = 0 :=
    (localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω L
      (Additive.ofMul (rationalPrimePrimeUnit p hp))).mpr
        (rationalPrimeOriginalCyclotomicClosure_exists_prime_norm p hp hp2 n a u hu ha)
  simpa using congrArg Additive.toMul hzero

end
end Dubon2026
