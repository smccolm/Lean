import Dubon2026.DeterminantCoefficientLaw
import Dubon2026.RepresentationDeterminantConjugacy

/-! # Natural multiplicative homogeneous determinant laws on the actual group algebra -/

namespace Dubon2026

noncomputable section
open Matrix

universe u v w z u'

/-- A determinant law is its multiplicative family on coefficient algebras in an arbitrary chosen universe, with naturality and degree required over every extension in that universe. -/
@[ext]
structure GroupDeterminantLaw (R : Type u) (G : Type v) [CommRing R] [Group G] (d : ℕ) where
  /-- The actual family on coefficient extensions of the original group algebra. -/
  eval : ∀ (S : Type w) [CommRing S], (R →+* S) → MonoidAlgebra S G →* S
  /-- Naturality under every homomorphism of coefficient extensions. -/
  natural : ∀ (S T : Type w) [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (x : MonoidAlgebra S G),
    ψ (eval S φ x) = eval T (ψ.comp φ) (MonoidAlgebra.mapRingHom G ψ x)
  /-- The precise homogeneous degree holds over every coefficient extension. -/
  homogeneous : ∀ (S : Type w) [CommRing S] (φ : R →+* S)
    (a : S) (x : MonoidAlgebra S G), eval S φ (a • x) = a ^ d * eval S φ x

variable {R : Type u} {G : Type v} {ι : Type z}
    [CommRing R] [Group G] [Fintype ι] [DecidableEq ι]

/-- Extend an actual determinant law along a coefficient homomorphism by evaluating on the composite extension. -/
def GroupDeterminantLaw.baseChange {S : Type u'} [CommRing S] {d : ℕ}
    (D : GroupDeterminantLaw.{u, v, w} R G d) (φ : R →+* S) :
    GroupDeterminantLaw.{u', v, w} S G d where
  eval T _ θ := D.eval T (θ.comp φ)
  natural T U _ _ θ ψ x := by
    simpa only [RingHom.comp_assoc] using D.natural T U (θ.comp φ) ψ x
  homogeneous T _ θ a x := D.homogeneous T (θ.comp φ) a x

/-- The original matrix representation gives an actual determinant law by the literal matrix determinant at every extension. -/
def matrixGroupDeterminantLaw (ρ : G →* GeneralLinearGroup ι R) :
    GroupDeterminantLaw.{u, v, w} R G (Fintype.card ι) where
  eval S _ φ := determinantCoefficientLaw (S := S) ρ φ
  natural S T _ _ φ ψ x := determinantCoefficientLaw_natural (S := S) (T := T) ρ φ ψ x
  homogeneous S _ φ a x := determinantCoefficientLaw_homogeneous (S := S) ρ φ a x

/-- The constructed law evaluates to the original group-algebra matrix determinant, not an independently chosen family. -/
theorem matrixGroupDeterminantLaw_eval (ρ : G →* GeneralLinearGroup ι R)
    (S : Type w) [CommRing S] (φ : R →+* S) (x : MonoidAlgebra S G) :
    (matrixGroupDeterminantLaw ρ).eval S φ x =
      Matrix.det (groupAlgebraMatrix ((GeneralLinearGroup.map φ).comp ρ) x) := rfl

/-- Original conjugate matrix representations define exactly the same determinant law over all coefficient extensions. -/
theorem matrixGroupDeterminantLaw_conjugate (ρ σ : G →* GeneralLinearGroup ι R)
    (A : GeneralLinearGroup ι R) (h : ∀ g, σ g = A * ρ g * A⁻¹) :
    (matrixGroupDeterminantLaw σ : GroupDeterminantLaw.{u, v, w} R G (Fintype.card ι)) =
      matrixGroupDeterminantLaw ρ := by
  apply GroupDeterminantLaw.ext
  funext S inst φ
  apply MonoidHom.ext
  intro x
  exact determinantCoefficientLaw_conjugate ρ σ A h φ x

/-- The constructed determinant law commutes with actual coefficient reduction of the original representation. -/
theorem matrixGroupDeterminantLaw_baseChange {S : Type u'} [CommRing S]
    (ρ : G →* GeneralLinearGroup ι R) (φ : R →+* S) :
    (matrixGroupDeterminantLaw ρ : GroupDeterminantLaw.{u, v, w} R G (Fintype.card ι)).baseChange φ =
      matrixGroupDeterminantLaw ((GeneralLinearGroup.map φ).comp ρ) := by
  apply GroupDeterminantLaw.ext
  funext T inst θ
  apply MonoidHom.ext
  intro x
  rfl

end
end Dubon2026
