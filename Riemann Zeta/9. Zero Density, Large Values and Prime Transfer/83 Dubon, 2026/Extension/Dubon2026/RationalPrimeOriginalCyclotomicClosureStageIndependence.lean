import Dubon2026.RationalPrimeChangedCyclotomicClosureFrobenius

/-! # Independence of the actual cyclotomic closure stage

The changed-uniformizer construction chooses an algebraic-closure embedding
separately for every natural unit.  The prime-power cyclotomic factor is a
finite Galois extension, so normality forces all of those embedded factors to
have the same actual field range.  The resulting automorphism of that one
fixed stage carries the primitive root chosen in one construction to the root
chosen in any other construction.

Since the stage Galois group is cyclic at an odd prime, this transport
automorphism commutes with every reciprocity value.  An action formula proved
for one chosen closure root therefore transports to every other chosen root.
This is the fixed-stage bridge needed to combine numerator and denominator
actions in the remaining rational-unit reciprocity calculation.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 800000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- The cyclotomic-factor embedding cut out of the finite ambient embedding
used for a particular natural unit. -/
def rationalPrimeOriginalCyclotomicClosureEmbedding
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeOriginalCyclotomicStage p hp n →ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp :=
  (rationalPrimeChangedCyclotomicFiniteAmbientEmbedding p hp n a u hu ha).comp
    (IntermediateField.inclusion (show
      (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField ≤
        rationalPrimeChangedCyclotomicFiniteAmbient p hp n u from le_sup_right))

/-- The separately chosen closure embeddings for two natural units cut out
the same finite Galois intermediate field. -/
theorem rationalPrimeOriginalCyclotomicClosureStage_eq
    (p : ℕ) (hp : p.Prime) (n a c : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (v : 𝒪[rationalPrimeLocalField p hp]ˣ) (hv : v.val = c) (hc : ¬p ∣ c) :
    rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha =
      rationalPrimeOriginalCyclotomicClosureStage p hp n c v hv hc := by
  change finiteGaloisEmbeddingStage
      (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n a u hu ha) =
    finiteGaloisEmbeddingStage
      (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n c v hv hc)
  exact finiteGaloisEmbeddingStage_eq _ _

/-- The automorphism of the fixed cyclotomic closure stage carrying the
realization selected for `a` to the realization selected for `c`. -/
def rationalPrimeOriginalCyclotomicClosureStageAut
    (p : ℕ) (hp : p.Prime) (n a c : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (v : 𝒪[rationalPrimeLocalField p hp]ˣ) (hv : v.val = c) (hc : ¬p ∣ c) :
    Gal(rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha /
      rationalPrimeLocalField p hp) :=
  finiteGaloisEmbeddingStageAut
    (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n a u hu ha)
    (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n c v hv hc)

/-- The fixed-stage transport automorphism sends the first actual primitive
root to the second one inside the original local closure. -/
theorem rationalPrimeOriginalCyclotomicClosureStageAut_root
    (p : ℕ) (hp : p.Prime) (n a c : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (v : 𝒪[rationalPrimeLocalField p hp]ˣ) (hv : v.val = c) (hc : ¬p ∣ c) :
    ((rationalPrimeOriginalCyclotomicClosureStageAut
        p hp n a c u hu ha v hv hc
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) :
      rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp) =
    ((rationalPrimeOriginalCyclotomicClosureRoot p hp n c v hv hc :
      rationalPrimeOriginalCyclotomicClosureStage p hp n c v hv hc) :
      rationalPrimeLocalClosure p hp) := by
  exact finiteGaloisEmbeddingStageAut_apply
    (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n a u hu ha)
    (rationalPrimeOriginalCyclotomicClosureEmbedding p hp n c v hv hc)
    (rationalPrimeOriginalCyclotomicStageRoot p hp n)

attribute [local instance] IsCyclic.commGroup

/-- Any power action on the first closure root transports to the second root.
The automorphism `g` is unchanged: cyclicity makes it commute with the stage
automorphism relating the two choices. -/
theorem rationalPrimeOriginalCyclotomicClosure_root_action_transport
    (p : ℕ) (hp : p.Prime) (n a c b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (v : 𝒪[rationalPrimeLocalField p hp]ˣ) (hv : v.val = c) (hc : ¬p ∣ c)
    [IsCyclic Gal(rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha /
      rationalPrimeLocalField p hp)]
    (g : Gal(rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha /
      rationalPrimeLocalField p hp))
    (h : ((g (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) =
      (((rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp)) :
    ((g (rationalPrimeOriginalCyclotomicClosureStageAut
        p hp n a c u hu ha v hv hc
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)) :
      rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp) =
    ((((rationalPrimeOriginalCyclotomicClosureRoot p hp n c v hv hc) ^ b) :
      rationalPrimeOriginalCyclotomicClosureStage p hp n c v hv hc) :
      rationalPrimeLocalClosure p hp) := by
  let τ := rationalPrimeOriginalCyclotomicClosureStageAut
    p hp n a c u hu ha v hv hc
  have hcomm : g * τ = τ * g := mul_comm g τ
  calc
    ((g (τ (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)) :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) =
      ((τ (g (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)) :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) := by
          exact congrArg Subtype.val
            (DFunLike.congr_fun hcomm
              (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha))
    _ = ((τ ((rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b) :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) := by
          have hsub : g (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
              (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b :=
            Subtype.ext h
          rw [hsub]
    _ = (((τ (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)) ^ b :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) := by rw [map_pow]
    _ = ((((rationalPrimeOriginalCyclotomicClosureRoot p hp n c v hv hc) ^ b) :
        rationalPrimeOriginalCyclotomicClosureStage p hp n c v hv hc) :
        rationalPrimeLocalClosure p hp) := by
          have hroot := rationalPrimeOriginalCyclotomicClosureStageAut_root
            p hp n a c u hu ha v hv hc
          simpa only [τ, map_pow] using
            congrArg (fun z : rationalPrimeLocalClosure p hp => z ^ b) hroot

end
end Dubon2026
