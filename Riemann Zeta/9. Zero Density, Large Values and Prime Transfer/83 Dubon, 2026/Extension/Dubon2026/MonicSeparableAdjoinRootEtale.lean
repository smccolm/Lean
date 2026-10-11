import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.Separable

/-! # The actual root algebra of a monic separable polynomial is étale -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- The genuine quotient `R[X]/(f)` of a monic separable polynomial is étale.
The proof compares its actual universal maps with a standard étale algebra. -/
theorem monic_separable_adjoinRoot_etale {R : Type} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := (Polynomial.separable_def f).mp hs
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hf
      g := 1
      cond := ⟨b, a, 0, by simpa [mul_comm, add_comm] using hab⟩ }
  let toRoot : P.Ring →ₐ[R] AdjoinRoot f := P.lift (AdjoinRoot.root f)
    ⟨by simp [P, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp [P]⟩
  let fromRoot : AdjoinRoot f →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  have hleft : fromRoot.comp toRoot = AlgHom.id R P.Ring := by
    apply P.hom_ext
    simp [toRoot, fromRoot]
  have hright : toRoot.comp fromRoot = AlgHom.id R (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext
    simp [toRoot, fromRoot]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom toRoot fromRoot hright hleft)

end
end Dubon2026
