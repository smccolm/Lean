import Dubon2026.OriginalRelationObstructionPairing
import Dubon2026.RationalCyclicInvariantLift

/-! # Prime-field readout of the original relation obstruction

The literal rational-circle embedding reads the invariant of the same
H1-to-H2 obstruction. Injectivity retains exact zero detection, needed
when DUB-17 converts its finite extension dichotomy into scalar duality.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G : Type} [Group G] (B C : Rep ℤ G)

/-- Concrete invariant and scalar readout of the original relation obstruction.
This data type alone asserts no existence or arithmetic duality result. -/
structure OriginalRelationPrimePairingData (p : ℕ) [NeZero p] where
  /-- The actual class-H2 invariant in the rational circle. -/
  invariant : groupCohomology C 2 →+ AddCircle (1 : ℚ)
  /-- The invariant detects equality of original class-H2 elements. -/
  invariant_injective : Function.Injective invariant
  /-- The additive residue-ring functional on original relation morphisms and H1 classes. -/
  readout : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p)
  /-- The literal rational cyclic embedding recovers the invariant of the obstruction. -/
  formula : ∀ φ y, rationalCyclicInvariant p (readout φ y) =
    invariant ((originalRelationExtensionObstruction B C φ).hom y)
  /-- The scalar functional detects exactly the original obstruction's zero locus. -/
  zero_iff : ∀ φ y, readout φ y = 0 ↔
    (originalRelationExtensionObstruction B C φ).hom y = 0

/-- The actual injective class invariant yields an additive prime-field
pairing with precisely the original obstruction kernel. -/
theorem originalRelation_exists_prime_invariant_pairing
    (p : ℕ) [NeZero p] (hB : ∀ b : B, p • b = 0)
    (inv : groupCohomology C 2 →+ AddCircle (1 : ℚ)) (hi : Function.Injective inv) :
    ∃ α : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p),
      (∀ φ y, rationalCyclicInvariant p (α φ y) =
        inv ((originalRelationExtensionObstruction B C φ).hom y)) ∧
      ∀ φ y, α φ y = 0 ↔ (originalRelationExtensionObstruction B C φ).hom y = 0 := by
  let f := originalRelationInvariantPairing B C inv
  have hf (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
      p • f φ y = 0 := by
    rw [← map_nsmul, originalH1_nsmul_zero B p hB, map_zero]
  have he (φ : originalRelationModule B ⟶ C) :=
    rationalCyclicInvariant_exists_lift p (f φ) (hf φ)
  let α : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p) := {
    toFun := fun φ => (he φ).choose
    map_zero' := by
      ext y
      apply rationalCyclicInvariant_injective p
      rw [(he 0).choose_spec]
      simp
    map_add' := fun φ ψ => by
      ext y
      apply rationalCyclicInvariant_injective p
      rw [(he (φ + ψ)).choose_spec]
      simp only [map_add, AddMonoidHom.add_apply,
        (he φ).choose_spec, (he ψ).choose_spec] }
  have hα (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
      rationalCyclicInvariant p (α φ y) = f φ y := (he φ).choose_spec y
  refine ⟨α, hα, fun φ y => ?_⟩
  rw [← originalRelationInvariantPairing_eq_zero_iff B C inv hi φ y]
  constructor
  · intro h
    rw [← hα, h, map_zero]
  · intro h
    apply rationalCyclicInvariant_injective p
    rw [hα, map_zero]
    exact h

/-- Consume a constructed invariant before specializing the coefficient,
retaining both the invariant and the exact scalar obstruction readout. -/
theorem originalRelation_exists_prime_pairing_from_invariant
    (p : ℕ) [NeZero p] (hB : ∀ b : B, p • b = 0)
    (h : ∃ inv : groupCohomology C 2 →+ AddCircle (1 : ℚ), Function.Injective inv) :
    ∃ inv : groupCohomology C 2 →+ AddCircle (1 : ℚ), Function.Injective inv ∧
      ∃ α : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p),
        (∀ φ y, rationalCyclicInvariant p (α φ y) =
          inv ((originalRelationExtensionObstruction B C φ).hom y)) ∧
        ∀ φ y, α φ y = 0 ↔ (originalRelationExtensionObstruction B C φ).hom y = 0 := by
  obtain ⟨inv, hi⟩ := h
  exact ⟨inv, hi, originalRelation_exists_prime_invariant_pairing B C p hB inv hi⟩

/-- Construct the complete pairing data from the actual coefficient
annihilator and a constructed injective class invariant. -/
theorem originalRelationPrimePairingData_nonempty
    (p : ℕ) [NeZero p] (hB : ∀ b : B, p • b = 0)
    (h : ∃ inv : groupCohomology C 2 →+ AddCircle (1 : ℚ), Function.Injective inv) :
    Nonempty (OriginalRelationPrimePairingData B C p) := by
  obtain ⟨inv, hi⟩ := h
  obtain ⟨α, hf, hz⟩ := originalRelation_exists_prime_invariant_pairing B C p hB inv hi
  exact ⟨⟨inv, hi, α, hf, hz⟩⟩

end
end Dubon2026
