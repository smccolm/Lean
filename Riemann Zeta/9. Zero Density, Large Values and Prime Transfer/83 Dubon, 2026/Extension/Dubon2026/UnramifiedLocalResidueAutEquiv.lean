import Dubon2026.LocalAlgebraAutResidueHom
import Dubon2026.UnramifiedSeparatedResidueFaithfulness

/-! # Original unramified local algebra automorphisms equal actual residue automorphisms -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] [IsHausdorff (maximalIdeal S) S]

/-- The original residue action is injective by actual formal unramifiedness
and original adic separatedness, without a separate inertia certificate. -/
theorem unramifiedLocalAlgebraAutResidueHom_injective :
    Function.Injective (localAlgebraAutResidueHom (R := R) (S := S)) := by
  intro f g h
  apply unramifiedSeparated_algEquiv_eq_of_residue f g
  intro x
  have hx := congrArg (fun e : ResidueField S ≃ₐ[ResidueField R] ResidueField S =>
    e (residue S x)) h
  simpa only [localAlgebraAutResidueHom_apply] using hx

variable [Finite (S ≃ₐ[R] S)] [Algebra.IsInvariant R S (S ≃ₐ[R] S)]

/-- The actual original local algebra and residue automorphism groups are
equivalent, combining genuine residue surjectivity and unramified uniqueness. -/
def unramifiedLocalResidueAutEquiv : (S ≃ₐ[R] S) ≃*
    (ResidueField S ≃ₐ[ResidueField R] ResidueField S) :=
  MulEquiv.ofBijective localAlgebraAutResidueHom
    ⟨unramifiedLocalAlgebraAutResidueHom_injective, localAlgebraAutResidueHom_surjective⟩

/-- The original equivalence sends a genuine local automorphism to its
actual action on original residue classes. -/
theorem unramifiedLocalResidueAutEquiv_apply (g : S ≃ₐ[R] S) (x : S) :
    unramifiedLocalResidueAutEquiv g (residue S x) = residue S (g x) := by
  rfl

end
end Dubon2026
