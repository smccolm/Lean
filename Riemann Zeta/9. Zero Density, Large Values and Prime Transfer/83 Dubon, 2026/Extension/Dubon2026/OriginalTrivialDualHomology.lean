import Dubon2026.OriginalFundamentalHomologyWitness
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-! # Actual homology of the trivial integral dual

Pinned internal-Hom unit and first-homology theorems identify the
literal trivial dual with the additive abelianization. This is the
group-order input to DUB-17's actual abelian norm-index route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Pinned internal-Hom unit and H1 comparisons identify the actual trivial integral dual homology with the abelianization. -/
def originalTrivialDualHomologyEquiv (G : Type) [Group G] :
    groupHomology ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj (Rep.trivial ℤ G ℤ)) 1 ≃+
      Additive (Abelianization G) :=
  (((groupHomology.functor ℤ G 1).mapIso
    (MonoidalClosed.unitIsoSelf (X := Rep.trivial ℤ G ℤ))).toLinearEquiv.toAddEquiv.trans
      (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ))).trans
        (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

end
end Dubon2026
