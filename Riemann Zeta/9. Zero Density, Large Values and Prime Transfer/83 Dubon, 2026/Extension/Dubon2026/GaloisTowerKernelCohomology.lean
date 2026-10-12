import Dubon2026.FiniteGaloisUnitTowerInflation
import Dubon2026.OriginalGroupCohomologyReindex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # The original automorphism restriction kernel and its genuine unit H1 -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Normal K L]

/-- The original automorphism restriction kernel is the actual Galois
group over the middle field, with precisely the same field automorphisms. -/
def galoisTowerKernelEquiv :
    (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker ≃* Gal(M/L) where
  toFun g := {
    __ := g.val.toRingEquiv
    commutes' r := by
      have h := congrArg (fun t : Gal(L/K) => t r) g.property
      exact (AlgEquiv.restrictNormal_commutes g.val L r).symm.trans
        (congrArg (algebraMap L M) h) }
  invFun g := ⟨g.restrictScalars K, by
    apply AlgEquiv.ext
    intro r
    apply (algebraMap L M).injective
    exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L r).trans (g.commutes r)⟩
  left_inv g := by apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
  right_inv g := by apply AlgEquiv.ext; intro x; rfl
  map_mul' g h := by apply AlgEquiv.ext; intro x; rfl

/-- This identification leaves every original extension-field value
unchanged; only its actual base-field automorphism type changes. -/
theorem galoisTowerKernelEquiv_apply
    (g : (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker) (x : M) :
    galoisTowerKernelEquiv K L M g x = g.val x := by
  rfl

/-- The original unit representations coincide under the actual kernel
identification, through the identity on extension-field units. -/
def galoisTowerKernelUnitCoefficientIso :
    Rep.res (galoisTowerKernelEquiv K L M).toMonoidHom (Rep.ofAlgebraAutOnUnits L M) ≅
      Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (Rep.ofAlgebraAutOnUnits K M) :=
  Rep.mkIso { __ := LinearEquiv.refl ℤ (Additive Mˣ)
              isIntertwining' g := by ext x; rfl }

/-- Hilbert90 for the actual upper field extension gives vanishing H1
of the original restriction kernel acting on the original upper-field units. -/
theorem galoisTowerKernelUnit_first_zero [FiniteDimensional L M] :
    Limits.IsZero (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (Rep.ofAlgebraAutOnUnits K M)) 1) := by
  let e := originalCohomologyReindex (Rep.ofAlgebraAutOnUnits L M)
      (galoisTowerKernelEquiv K L M) 1 ≪≫
    (groupCohomology.functor ℤ
      (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker 1).mapIso
        (galoisTowerKernelUnitCoefficientIso K L M)
  have hz : Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits L M) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact Limits.IsZero.of_iso hz e.symm

end
end Dubon2026
