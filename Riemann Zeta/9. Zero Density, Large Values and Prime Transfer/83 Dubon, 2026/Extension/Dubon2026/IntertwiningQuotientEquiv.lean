import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Complex.Basic

/-! # The genuine quotient representation of a surjective original intertwiner -/

namespace Dubon2026

noncomputable section

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (T : Representation.IntertwiningMap ρ σ)

/-- The literal kernel of an original intertwiner is stable under its original source action. -/
theorem intertwiningKernel_invariant (g : G) (x : V) (hx : T.toLinearMap x = 0) :
    T.toLinearMap (ρ g x) = 0 := by
  change T (ρ g x) = 0
  rw [Representation.IntertwiningMap.isIntertwining, show T x = 0 from hx, map_zero]

/-- The original source action on its actual quotient by the genuine intertwiner kernel. -/
def intertwiningQuotientRepresentation : Representation ℂ G (V ⧸ T.toLinearMap.ker) :=
  ρ.quotient T.toLinearMap.ker (fun g x hx => intertwiningKernel_invariant ρ σ T g x hx)

/-- The first-isomorphism equivalence genuinely intertwines the original quotient action. -/
theorem intertwiningQuotientEquiv_intertwines (hs : Function.Surjective T)
    (g : G) (x : V ⧸ T.toLinearMap.ker) :
    T.toLinearMap.quotKerEquivOfSurjective hs (intertwiningQuotientRepresentation ρ σ T g x) =
      σ g (T.toLinearMap.quotKerEquivOfSurjective hs x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change T (ρ g x) = σ g (T x)
    exact Representation.IntertwiningMap.isIntertwining ρ σ T g x

/-- A surjective original intertwiner identifies its actual kernel quotient as an equivalent group representation, with the quotient action proved equivariant. -/
def intertwiningQuotientEquiv (hs : Function.Surjective T) :
    Representation.Equiv (intertwiningQuotientRepresentation ρ σ T) σ :=
  Representation.Equiv.mk (T.toLinearMap.quotKerEquivOfSurjective hs) (fun g => by
    apply LinearMap.ext
    intro x
    exact intertwiningQuotientEquiv_intertwines ρ σ T hs g x)

/-- The genuine quotient equivalence sends each original quotient class to its actual intertwiner value. -/
theorem intertwiningQuotientEquiv_mk (hs : Function.Surjective T) (x : V) :
    intertwiningQuotientEquiv ρ σ T hs (Submodule.Quotient.mk x) = T x := rfl

end
end Dubon2026
