/-
Suggested Lean forms for PotentialAutomorphyInfrastructurePartII, PL.7.

This file is not the roadmap and is not exhaustive. The reader document
research/blueprint/readmes/PotentialAutomorphyInfrastructurePartII--PL.7.md is definitive.
These statements suggest names and signatures for contributors and reviewers. Proofs use
sorry and make no implementation claim. The pinned libraries are Mathlib 082e2d3 and
Tau Ceti f790474.

The two new definitions and all their API and tests are expressed using native objects.
The algebraic prime predicate is parametrised by the permitted-extension index: its
arithmetic specialisation indexes precisely the good extensions, with J_M obtained from
the Hecke kernel in P_M. The diagram is R <- P -> T, not a homomorphism R -> T.

Imported interfaces are named explicitly. No unavailable condition is replaced by an
uninterpreted proposition. The theorem blocks identify the arithmetic hypotheses omitted
from their signatures: elaboration checks these proposed interfaces, not the omitted
conditions or the recorded source-proof boundaries. In particular weak primitivity is
never silently strengthened. See the reader's signature limitations for each theorem.
-/
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.NumberTheory.NumberField.SplitsCompletely

noncomputable section
open scoped NumberField
open NumberField

namespace TauCeti.Automorphy.PL7

/-! ## Good extensions -/

section Good
variable {L Ω : Type*} [Field L] [NumberField L] [Field Ω] [CharZero Ω]
  [Algebra L Ω] [IsAlgClosed Ω]
variable (M E : IntermediateField L Ω) [FiniteDimensional L M]

/-- PL.7/good-cm-extension. Finiteness is an instance on M; Ω is an algebraic closure
or an algebraically closed ambient field. X is a set of nonzero finite primes in uses. -/
def IsGoodExtension (X : Set (Ideal (𝓞 L))) : Prop :=
  letI : NumberField M := NumberField.of_module_finite L M
  NumberField.IsCMField M ∧
  Group.IsSolvable ((IntermediateField.normalClosure L M Ω) ≃ₐ[L]
    (IntermediateField.normalClosure L M Ω)) ∧
  M.LinearDisjoint E ∧
  ∀ P ∈ X, (Ideal.primesOver P (𝓞 M)).ncard = Module.finrank L M

namespace IsGoodExtension

theorem iff_conditions (X : Set (Ideal (𝓞 L))) :
    IsGoodExtension M E X ↔
    (letI : NumberField M := NumberField.of_module_finite L M
     NumberField.IsCMField M ∧
     Group.IsSolvable ((IntermediateField.normalClosure L M Ω) ≃ₐ[L]
       (IntermediateField.normalClosure L M Ω)) ∧
     M.LinearDisjoint E ∧
     ∀ P ∈ X, (Ideal.primesOver P (𝓞 M)).ncard = Module.finrank L M) := by
  sorry

theorem self [NumberField.IsCMField L] (X : Set (Ideal (𝓞 L)))
    (hX : ∀ P ∈ X, P.IsPrime ∧ P ≠ ⊥) :
    IsGoodExtension (⊥ : IntermediateField L Ω) E X := by
  sorry

theorem linearDisjoint {X : Set (Ideal (𝓞 L))} (h : IsGoodExtension M E X) :
    M.LinearDisjoint E := by
  sorry

theorem splits {X : Set (Ideal (𝓞 L))} (h : IsGoodExtension M E X)
    (P : Ideal (𝓞 L)) (hP : P ∈ X) :
    letI : NumberField M := NumberField.of_module_finite L M
    (Ideal.primesOver P (𝓞 M)).ncard = Module.finrank L M := by
  sorry

theorem mono_split_set {X X' : Set (Ideal (𝓞 L))} (h : IsGoodExtension M E X)
    (hX : X' ⊆ X) : IsGoodExtension M E X' := by
  sorry

/-- Goodness composes through the compositum avoidance field E M. -/
theorem tower [NumberField.IsCMField L] (N : IntermediateField M Ω)
    [FiniteDimensional M N] [FiniteDimensional L (N.restrictScalars L)]
    (X : Set (Ideal (𝓞 L))) (hX : ∀ P ∈ X, P.IsPrime ∧ P ≠ ⊥)
    (hM : IsGoodExtension M E X) :
    letI : NumberField M := NumberField.of_module_finite L M
    letI : NumberField.IsCMField M := hM.1
    IsGoodExtension N (IntermediateField.adjoin M (E : Set Ω))
      {Q | ∃ P ∈ X, Q ∈ Ideal.primesOver P (𝓞 M)} →
    IsGoodExtension (N.restrictScalars L) E X := by
  sorry

end IsGoodExtension

-- test: good_self
example [NumberField.IsCMField L] (X : Set (Ideal (𝓞 L)))
    (hX : ∀ P ∈ X, P.IsPrime ∧ P ≠ ⊥) :
    IsGoodExtension (⊥ : IntermediateField L Ω) E X := by
  sorry

-- test: not_good_meets_avoid
example (hdegree : 1 < Module.finrank L M) (X : Set (Ideal (𝓞 L))) :
    ¬ IsGoodExtension M M X := by
  sorry

-- test: not_good_bad_split
example (X : Set (Ideal (𝓞 L))) (P : Ideal (𝓞 L)) (hP : P ∈ X) :
    letI : NumberField M := NumberField.of_module_finite L M
    (Ideal.primesOver P (𝓞 M)).ncard ≠ Module.finrank L M →
    ¬ IsGoodExtension M E X := by
  sorry

-- test: good_empty_split_set
example : IsGoodExtension M E ∅ ↔
    (NumberField.IsCMField M ∧
     Group.IsSolvable ((IntermediateField.normalClosure L M Ω) ≃ₐ[L]
       (IntermediateField.normalClosure L M Ω)) ∧ M.LinearDisjoint E) := by
  sorry

-- test: good_galois_splitting
example [IsGalois L M] (X : Set (Ideal (𝓞 L))) (P : Ideal (𝓞 L)) [P.IsMaximal]
    (hP : P ∈ X) (h : IsGoodExtension M E X) :
    letI : NumberField M := NumberField.of_module_finite L M
    P.ramificationIdxIn (𝓞 M) = 1 ∧ P.inertiaDegIn (𝓞 M) = 1 := by
  sorry

end Good

/-! ## Potential pro-automorphy -/

section Potential
variable {P R : Type*} [CommRing P] [CommRing R] {I : Type*}
variable (θ : P →+* R) (J : I → Ideal P)

/-- PL.7/potentially-pro-automorphic-prime. In arithmetic I consists of good extensions. -/
def IsPotentiallyProAutomorphic (p : PrimeSpectrum R) : Prop :=
  ∃ i, Ideal.map θ (J i) ≤ p.asIdeal

namespace IsPotentiallyProAutomorphic

theorem iff_comap (p : PrimeSpectrum R) :
    IsPotentiallyProAutomorphic θ J p ↔ ∃ i, J i ≤ Ideal.comap θ p.asIdeal := by
  sorry

theorem of_witness (p : PrimeSpectrum R) (i : I)
    (hi : Ideal.map θ (J i) ≤ p.asIdeal) : IsPotentiallyProAutomorphic θ J p := by
  sorry

theorem mono_prime (p q : PrimeSpectrum R) (h : IsPotentiallyProAutomorphic θ J p)
    (hpq : p.asIdeal ≤ q.asIdeal) : IsPotentiallyProAutomorphic θ J q := by
  sorry

theorem mono_ideals (J' : I → Ideal P) (hJ : ∀ i, J' i ≤ J i)
    (p : PrimeSpectrum R) (h : IsPotentiallyProAutomorphic θ J p) :
    IsPotentiallyProAutomorphic θ J' p := by
  sorry

theorem of_tower (p : PrimeSpectrum R) (i j : I)
    (hi : Ideal.map θ (J i) ≤ p.asIdeal) (hji : J j ≤ J i) :
    Ideal.map θ (J j) ≤ p.asIdeal := by
  sorry

theorem ext (J' : I → Ideal P) (hJ : ∀ i, Ideal.map θ (J i) = Ideal.map θ (J' i)) :
    IsPotentiallyProAutomorphic θ J = IsPotentiallyProAutomorphic θ J' := by
  sorry

-- test: potential_empty_index
example (J₀ : Empty → Ideal P) (p : PrimeSpectrum R) :
    ¬ IsPotentiallyProAutomorphic θ J₀ p := by
  sorry

-- test: potential_zero_ideal
example (p : PrimeSpectrum R) :
    IsPotentiallyProAutomorphic θ (fun _ : Unit => (⊥ : Ideal P)) p := by
  sorry

-- test: potential_unit_ideal
example (p : PrimeSpectrum R) :
    ¬ IsPotentiallyProAutomorphic θ (fun _ : I => (⊤ : Ideal P)) p := by
  sorry

-- test: potential_quotient_kernel
example (p : PrimeSpectrum (ZMod 2)) (hp : p.asIdeal = ⊥) :
    IsPotentiallyProAutomorphic (Int.castRingHom (ZMod 2))
      (fun _ : Unit => Ideal.span ({(2 : ℤ)} : Set ℤ)) p := by
  sorry

end IsPotentiallyProAutomorphic
end Potential

/-! ## Imported representation interfaces

The following real predicates are the parent PL.6 definitions, repeated here solely to
make this standalone prototype elaborate. They are imported targets, not PL.7 nodes.
-/

abbrev Gal (F : Type*) [Field F] := Field.absoluteGaloisGroup F

def stdRep {G A : Type*} [Monoid G] [CommRing A] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) A) :
    Representation A G (Fin n → A) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

def repBaseChange {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (K : Type*) [Field K] [Algebra k K] (ρ : Representation k G V) :
    Representation K G (TensorProduct k K V) where
  toFun g := (ρ g).baseChange K
  map_one' := by sorry
  map_mul' := by sorry

def IsAbsIrredRep {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  (repBaseChange (AlgebraicClosure k) ρ).IsIrreducible

def IsPrimitive {G k : Type*} [Group G] [TopologicalSpace G] [Field k] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) k) : Prop :=
  ∀ H : Subgroup G, IsOpen (H : Set G) → H ≠ ⊤ →
    ∀ (m : ℕ) (σ : H →* Matrix.GeneralLinearGroup (Fin m) k),
      IsOpen (σ.ker : Set H) →
      IsEmpty ((stdRep ρ).Equiv (Representation.ind H.subtype (stdRep σ)))

namespace Imported

/-- PL.0/automorphic-polarized-representation and PL.2/unitary-base-change-and-descent:
RACSDC representations with a chosen finite-K realization of their associated l-adic
representation. The ordinary weight condition is omitted, not encoded in this type. -/
def RACSDCModel (F K : Type*) [Field F] [NumberField F] [Field K] (n : ℕ) : Type := sorry

/-- The associated representation of the chosen realization, from the same parent owner. -/
def associated {F K : Type*} [Field F] [NumberField F] [Field K] {n : ℕ}
    (π : RACSDCModel F K n) : Gal F →* Matrix.GeneralLinearGroup (Fin n) K := sorry

end Imported

/-! ## Residual invariants and generic restriction -/

/-- PL.7/good-extension-residual-invariants, residual-image/weak-primitivity clauses.
The avoidance extension is identified with ker ρbar through the explicit image condition.
Omitted: its cyclotomic enlargement, CM quadratic independence, Schur and the strong
primitivity clause; those clauses use the parent PL.6 interfaces. -/
theorem good_extension_residual_invariants
    {L M k : Type*} [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra L M] [Field k] {n : ℕ}
    (ρbar : Gal L →* Matrix.GeneralLinearGroup (Fin n) k)
    (hcontinuous : IsOpen (ρbar.ker : Set (Gal L)))
    (himage : (ρbar.comp (Field.absoluteGaloisGroup.map (algebraMap L M)).toMonoidHom).range =
      ρbar.range) (hprimitive : IsPrimitive ρbar) :
    IsPrimitive (ρbar.comp (Field.absoluteGaloisGroup.map (algebraMap L M)).toMonoidHom) := by
  sorry

/-- PL.7/weak-primitive-generic-restriction. The source target, not a completed proof.
Omitted: continuity, the polarized extension to G_{F+,S}, Schur/cyclotomic and ramification
hypotheses, and the residual cyclotomic no-l-power-quotient condition. The eigenvalue
hypothesis and weak primitivity are expressed directly. K is a native field of fractions
of k[[T]]. No arbitrary-rank semisimplicity bridge is claimed. -/
theorem weak_primitive_generic_restriction
    {F k : Type*} [Field F] [NumberField F] [NumberField.IsCMField F] [Field k] [Finite k]
    (K : Type*) [Field K] [Algebra (PowerSeries k) K] [IsFractionRing (PowerSeries k) K]
    (l n : ℕ) [Fact l.Prime] [CharP k l] (hl : 3 < l) (hn : ¬ l ∣ n)
    (ρ : Gal F →* Matrix.GeneralLinearGroup (Fin n) (PowerSeries k))
    (hprimitive : IsPrimitive
      ((Matrix.GeneralLinearGroup.map (PowerSeries.constantCoeff (R := k))).comp ρ))
    (hirred : IsAbsIrredRep (stdRep
      ((Matrix.GeneralLinearGroup.map (algebraMap (PowerSeries k) K)).comp ρ)))
    (heigen : ∃ (σ : Gal F) (U : Matrix.GeneralLinearGroup (Fin n) (PowerSeries k))
      (α : Fin n → (PowerSeries k)ˣ),
      ((U⁻¹ * ρ σ * U : Matrix.GeneralLinearGroup (Fin n) (PowerSeries k)) :
        Matrix (Fin n) (Fin n) (PowerSeries k)) = Matrix.diagonal (fun i => (α i : PowerSeries k)) ∧
      ∀ m : Fin n → ℤ, (∏ i, (α i) ^ (m i)) = 1 → m = 0)
    (N : Subgroup (Gal F)) (hN : IsOpen (N : Set (Gal F))) :
    IsAbsIrredRep (stdRep
      (((Matrix.GeneralLinearGroup.map (algebraMap (PowerSeries k) K)).comp ρ).comp N.subtype)) := by
  sorry

/-! ## Prime propagation, connectedness and ring finiteness

Here R, P and T are the imported arithmetic rings, and I indexes the good extensions.
The precise unitary datum, generic representation and local conditions are specified in
the reader. They are omitted here rather than represented by unspecified Prop fields.
-/

section Rings
variable {Λ P R T : Type*} [CommRing Λ] [CommRing P] [CommRing R] [CommRing T]
  [Algebra Λ R] {I : Type*}

/-- PL.7/generic-potential-propagation.
D is [L+:Q] and r is |R|; the twist-degree bound is retained.
Omitted: genericity, residual invariants, triviality at R, q_v bounds and unitary setup. -/
theorem generic_potential_propagation (θ : P →+* R) (J : I → Ideal P)
    (D r : ℕ) (hdegree : r < D)
    (ϖ : R) (p : PrimeSpectrum R) (hchar : ϖ ∈ p.asIdeal)
    (hdim : ringKrullDim (R ⧸ p.asIdeal) = 1)
    (hauto : IsPotentiallyProAutomorphic θ J p)
    (Q : PrimeSpectrum R) (hQ : Q.asIdeal ∈ (⊥ : Ideal R).minimalPrimes)
    (hQp : Q.asIdeal ≤ p.asIdeal) : IsPotentiallyProAutomorphic θ J Q := by
  sorry

/-- PL.7/connectedness-ordinary-lifting, the all-component conclusion.
Omitted: unitary setup, generic-prime/connectedness hypotheses and the O-point classicality
conclusion and the q_v congruence bound at R. D is [L+:Q], r is the cardinality of R; the sufficient +3 bound is retained. -/
theorem connectedness_ordinary_lifting (θ : P →+* R) (J : I → Ideal P)
    (D n r d₀ d_l : ℕ) (hn : 2 ≤ n) (hd₀ : r * n * (n + 1) + 3 < d₀)
    (hdl : max (r * n * (n + 1) + 3) (n * (n - 1) / 2 + 1) < d_l)
    (Q : PrimeSpectrum R) (hQ : Q.asIdeal ∈ (⊥ : Ideal R).minimalPrimes) :
    IsPotentiallyProAutomorphic θ J Q := by
  sorry

/-- PL.7/connectedness-ring-finiteness, its general algebraic final step.
The arithmetic application obtains hcomponents from witnesses and finite restriction maps.
The nilradical lifting step already exists as
Module.finite_of_surjective_of_ker_le_nilradical; it is not a new roadmap target. -/
theorem connectedness_ring_finiteness [IsNoetherianRing Λ] [IsNoetherianRing R]
    (hcomponents : ∀ Q ∈ (⊥ : Ideal R).minimalPrimes, Module.Finite Λ (R ⧸ Q)) :
    Module.Finite Λ R := by
  sorry

/-- PL.7/weak-primitive-generic-r-equals-t, the kernel-containment conclusion.
Omitted: genericity, weak primitivity and all residual/local/unitary hypotheses.
The theorem does not construct a map R -> T. -/
theorem weak_primitive_generic_r_equals_t (θ : P →+* R) (η : P →+* T)
    (ϖ : R) (p Q : PrimeSpectrum R) (hchar : ϖ ∈ p.asIdeal)
    (hdim : ringKrullDim (R ⧸ p.asIdeal) = 1)
    (hhecke : Ideal.map θ (RingHom.ker η) ≤ p.asIdeal) (hQp : Q.asIdeal ≤ p.asIdeal) :
    Ideal.map θ (RingHom.ker η) ≤ Q.asIdeal := by
  sorry

/-- PL.7/source-primitive-ant-finiteness.
Omitted: the identity of R as the ordinary deformation ring, polarized seed, weak
primitivity, residual/local/global conditions and coefficient realization. -/
theorem source_primitive_ant_finiteness (l n : ℕ) [Fact l.Prime]
    (hl : 3 < l) (hn : 2 ≤ n) (hprime : ¬ l ∣ n) : Module.Finite Λ R := by
  sorry

/-- PL.7/auxiliary-place-ant-finiteness. A is the residual arithmetic Frobenius,
q its residue cardinality. Invertibility here expresses H^0(ad ρbar(1))=0.
Omitted: the original ordinary deformation/seed/residual hypotheses, local unramifiedness,
and the requested comparison between nonscalar auxiliary levels and deformation rings. -/
theorem auxiliary_place_ant_finiteness
    {k : Type*} [Field k] (l n q : ℕ) [Fact l.Prime] [CharP k l]
    (hl : 3 < l) (hn : 2 ≤ n) (hprime : ¬ l ∣ n)
    (A : Matrix.GeneralLinearGroup (Fin n) k)
    (hunobstructed : Function.Bijective (fun X : Matrix (Fin n) (Fin n) k =>
      (q : k) • ((A : Matrix (Fin n) (Fin n) k) * X *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) - X)) :
    Module.Finite Λ R := by
  sorry

end Rings

/-! ## Source-primitive automorphy conclusions

The integral representation has a residual map O -> k and a coefficient map O -> K.
The imported RACSDC realization is a mathematical type, not an unavailable predicate.
Ordinarity, ramification, polarization, local Steinberg and residual constituent conditions
are omitted from these signatures; their complete statements are in the reader.
-/

section Automorphy
variable {F O K k : Type*} [Field F] [NumberField F] [NumberField.IsCMField F]
  [CommRing O] [Field K] [CharZero K] [Field k]

/-- PL.7/source-primitive-ant-lifting. Weak primitivity is stated; the remainder of
ANT Theorem 6.1's arithmetic hypotheses are omitted as described above. The source
uses a polarized lattice with semisimple reduction; existence of that lattice is omitted. -/
theorem source_primitive_ant_lifting (l n : ℕ) [Fact l.Prime] [CharP k l]
    (hl : 3 < l) (hn : 2 ≤ n) (hprime : ¬ l ∣ n)
    (toK : O →+* K) (tok : O →+* k)
    (ρ : Gal F →* Matrix.GeneralLinearGroup (Fin n) O)
    (hprimitive : IsPrimitive ((Matrix.GeneralLinearGroup.map tok).comp ρ)) :
    ∃ π : Imported.RACSDCModel F K n,
      Nonempty ((stdRep (Imported.associated π)).Equiv
        (stdRep ((Matrix.GeneralLinearGroup.map toK).comp ρ))) := by
  sorry

/-- PL.7/source-primitive-two-constituent-lifting. Omitted: both adequate cyclotomic
constituents and their separate potential automorphy, as well as the ordinary/Steinberg
seed and polarization clauses. No F not-contained-in F+(ζ_l) clause is inserted. -/
theorem source_primitive_two_constituent_lifting (l n₁ n₂ : ℕ) [Fact l.Prime] [CharP k l]
    (hl : 3 < l) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hprime : ¬ l ∣ (n₁ + n₂))
    (toK : O →+* K) (tok : O →+* k)
    (ρ : Gal F →* Matrix.GeneralLinearGroup (Fin (n₁ + n₂)) O)
    (hprimitive : IsPrimitive ((Matrix.GeneralLinearGroup.map tok).comp ρ)) :
    ∃ π : Imported.RACSDCModel F K (n₁ + n₂),
      Nonempty ((stdRep (Imported.associated π)).Equiv
        (stdRep ((Matrix.GeneralLinearGroup.map toK).comp ρ))) := by
  sorry

end Automorphy

end TauCeti.Automorphy.PL7
