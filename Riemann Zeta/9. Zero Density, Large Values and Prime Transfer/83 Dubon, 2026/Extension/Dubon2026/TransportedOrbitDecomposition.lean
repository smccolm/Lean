import Dubon2026.TransportedOrbitCoinduction
import Dubon2026.FiniteProductCohomology
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The actual orbit decomposition of coherently transported products

Restriction to the original place orbits is equivariant, and each orbit
is identified with cohomology of its original stabilizer factor. This
connects the actual local-coordinate product to the finite and acyclic
orbit factors needed for DUB-17's supported-idele Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- The original coherent transport restricted to one actual orbit. -/
def transportedOrbitFactorRep (ω : MulAction.orbitRel.Quotient G ι) : Rep R G :=
  transportedPiRep R G ω.orbit (fun i => M i.val)
    (fun g i j h => T g i.val j.val (congrArg Subtype.val h))
    (fun i x => T_one i.val x)
    (fun g h i j k hh hg hgh x => T_mul g h i.val j.val k.val
      (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x)

/-- The actual stabilizer coefficient on an original orbit point. -/
def transportedOrbitPointRep (ω : MulAction.orbitRel.Quotient G ι) (i : ω.orbit) :
    Rep R (MulAction.stabilizer G i) :=
  transportedStabilizerRep R G ω.orbit (fun j => M j.val)
    (fun g j k h => T g j.val k.val (congrArg Subtype.val h))
    (fun j x => T_one j.val x)
    (fun g h j k l hh hg hgh x => T_mul g h j.val k.val l.val
      (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x) i

/-- Restriction to the original orbits is a linear equivalence on dependent coordinates. -/
def transportedOrbitLinearEquiv :
    (∀ i, M i) ≃ₗ[R] (∀ ω : MulAction.orbitRel.Quotient G ι, ∀ j : ω.orbit, M j.val) :=
  (LinearEquiv.piCongrLeft R M (MulAction.selfEquivSigmaOrbits' G ι).symm).symm |>.trans
    (LinearEquiv.piCurry R (fun (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) => M j.val))

/-- The original coordinate representation decomposes into its actual transported orbit factors. -/
def transportedOrbitProductIso :
    transportedPiRep R G ι M T T_one T_mul ≅
      originalPiRep (transportedOrbitFactorRep R G ι M T T_one T_mul) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk (transportedOrbitLinearEquiv R G ι M) ?_
  intro g
  apply LinearMap.ext
  intro x
  funext ω j
  rfl

/-- The representation decomposition is actual restriction to the original orbit. -/
theorem transportedOrbitProductIso_hom_apply (x : ∀ i, M i)
    (ω : MulAction.orbitRel.Quotient G ι) (j : ω.orbit) :
    (transportedOrbitProductIso R G ι M T T_one T_mul).hom.hom x ω j = x j.val := rfl

/-- The original orbit cohomology is that of the actual point-stabilizer coefficient. -/
def transportedOrbitFactorCohomologyIso
    (ω : MulAction.orbitRel.Quotient G ι) (i : ω.orbit) (n : ℕ) :
    groupCohomology (transportedOrbitFactorRep R G ι M T T_one T_mul ω) n ≅
      groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω i) n :=
  transportedOrbitCohomologyIso R G ω.orbit (fun j => M j.val)
    (fun g j k h => T g j.val k.val (congrArg Subtype.val h))
    (fun j x => T_one j.val x)
    (fun g h j k l hh hg hgh x => T_mul g h j.val k.val l.val
      (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x) i n

end
end Dubon2026
