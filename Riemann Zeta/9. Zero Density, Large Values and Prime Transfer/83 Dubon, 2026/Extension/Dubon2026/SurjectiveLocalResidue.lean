import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Actual residue algebra maps of original surjective local coefficient maps -/

namespace Dubon2026

noncomputable section

variable {O R S : Type*} [CommRing O] [CommRing R] [IsLocalRing R]
  [CommRing S] [IsLocalRing S] [Algebra O R] [Algebra O S]

/-- The genuine residue-field map retains the original coefficient algebra structure. -/
def localResidueAlgebraMap (f : R →ₐ[O] S) [IsLocalHom f.toRingHom] :
    IsLocalRing.ResidueField R →ₐ[O] IsLocalRing.ResidueField S :=
  { IsLocalRing.ResidueField.map f.toRingHom with
    commutes' := fun o => by
      change IsLocalRing.ResidueField.map f.toRingHom
        (IsLocalRing.residue R (algebraMap O R o)) =
          IsLocalRing.residue S (algebraMap O S o)
      rw [IsLocalRing.ResidueField.map_residue]
      exact congrArg (IsLocalRing.residue S) (f.commutes o) }

/-- The actual induced residue algebra map has the original residue value on every original coefficient. -/
theorem localResidueAlgebraMap_residue (f : R →ₐ[O] S) [IsLocalHom f.toRingHom]
    (r : R) :
    localResidueAlgebraMap f (IsLocalRing.residue R r) = IsLocalRing.residue S (f r) := rfl

/-- Surjectivity of the original coefficient map gives surjectivity on its actual residue fields. -/
theorem localResidueAlgebraMap_surjective (f : R →ₐ[O] S) [IsLocalHom f.toRingHom]
    (hf : Function.Surjective f) : Function.Surjective (localResidueAlgebraMap f) := by
  intro x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨IsLocalRing.residue R r, localResidueAlgebraMap_residue f r⟩

/-- An original surjective local coefficient map induces a genuine equivalence of its original residue algebras. -/
def surjectiveLocalResidueAlgEquiv (f : R →ₐ[O] S) [IsLocalHom f.toRingHom]
    (hf : Function.Surjective f) :
    IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField S :=
  AlgEquiv.ofBijective (localResidueAlgebraMap f)
    ⟨(localResidueAlgebraMap f).injective, localResidueAlgebraMap_surjective f hf⟩

/-- The genuine residue equivalence preserves the actual residue of every original coefficient. -/
theorem surjectiveLocalResidueAlgEquiv_residue (f : R →ₐ[O] S)
    [IsLocalHom f.toRingHom] (hf : Function.Surjective f) (r : R) :
    surjectiveLocalResidueAlgEquiv f hf (IsLocalRing.residue R r) =
      IsLocalRing.residue S (f r) := rfl

end
end Dubon2026
