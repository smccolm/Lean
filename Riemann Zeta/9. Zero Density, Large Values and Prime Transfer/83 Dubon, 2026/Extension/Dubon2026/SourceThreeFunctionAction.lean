import Dubon2026.SourceCupThreeEntries
import Dubon2026.SourceAffineFunctionHecke
import Dubon2026.SourcePrimeHeckeNaturality
import Dubon2026.SourcePrimeHeckeScalar
import Dubon2026.SourceTrivialCoefficientHecke

/-! The actual characteristic-three coefficient maps for the odd twist.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> characteristic-three odd twist. The existing affine function
representation acts by u minus the actual entry character. Its coefficient
difference intertwines Hecke with the exact prime twist.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (Q : ℕ) (h3Q : 3 ∣ Q)

include h3Q in
/-- In characteristic three the original affine coefficient action is translation
by the negative of the actual upper-right/lower-right entry character. -/
theorem sourceThreeFunctionAction_apply (g : Gamma0 Q) (f : ZMod 3 → F) (u : ZMod 3) :
    sourceAffineFunctionAction 3 Q F g f u = f (u - SourceCupThree.phi Q g) := by
  change f (sourceAffineD 3 Q g * (sourceAffineD 3 Q g * u - sourceAffineB 3 Q g)) = _
  congr 1
  have hd := SourceCupThree.d3_mul_d3 Q h3Q g
  dsimp only [SourceCupThree.phi]
  linear_combination u * hd

/-- The literal difference between translations by two and one on original functions. -/
def sourceThreeFunctionDifference : Module.End F (ZMod 3 → F) where
  toFun f u := f (u + 2) - f (u + 1)
  map_add' f g := by
    funext u
    dsimp
    ring
  map_smul' r f := by
    funext u
    change r * f (u + 2) - r * f (u + 1) = r * (f (u + 2) - f (u + 1))
    exact (mul_sub r _ _).symm

/-- The actual translation difference is equivariant for the original affine action. -/
def sourceThreeFunctionDifferenceMap :
    sourceAffineFunctionRep 3 Q F h3Q ⟶ sourceAffineFunctionRep 3 Q F h3Q :=
  Rep.ofHom {
    toLinearMap := sourceThreeFunctionDifference F
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro f
      change ZMod 3 → F at f
      funext u
      change sourceThreeFunctionDifference F (sourceAffineFunctionAction 3 Q F g f) u =
        sourceAffineFunctionAction 3 Q F g (sourceThreeFunctionDifference F f) u
      simp only [sourceThreeFunctionDifference, sourceThreeFunctionAction_apply F Q h3Q,
        LinearMap.coe_mk, AddHom.coe_mk]
      congr 2 <;> ring }

/-- Constants embed the original trivial coefficients into actual affine functions. -/
def sourceThreeConstantMap :
    Rep.trivial F (Gamma0 Q) F ⟶ sourceAffineFunctionRep 3 Q F h3Q :=
  Rep.ofHom {
    toLinearMap := {
      toFun := fun x _ => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

variable [CharP F 3]

/-- The actual coefficient difference intertwines the original Hecke rescaling
with exactly the good-prime scalar in characteristic three. -/
theorem sourceThreeFunctionDifference_diagonal (ell : ℕ) (hell : (ell : ZMod 3) ≠ 0) :
    (sourceThreeFunctionDifference F).comp (sourceAffineFunctionDiagonal 3 F ell) =
      (ell : F) • ((sourceAffineFunctionDiagonal 3 F ell).comp
        (sourceThreeFunctionDifference F)) := by
  apply LinearMap.ext
  intro f
  funext u
  change f ((ell : ZMod 3)⁻¹ * (u + 2)) - f ((ell : ZMod 3)⁻¹ * (u + 1)) =
    (ell : F) * (f ((ell : ZMod 3)⁻¹ * u + 2) - f ((ell : ZMod 3)⁻¹ * u + 1))
  have hc : (ell : F) = ZMod.castHom (dvd_refl 3) F (ell : ZMod 3) :=
    (map_natCast (ZMod.castHom (dvd_refl 3) F) ell).symm
  rw [hc]
  generalize (ell : ZMod 3) = a at hell ⊢
  have ha : a = 1 ∨ a = -1 := by
    fin_cases a
    · exact (hell rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · rw [inv_one, map_one]
    simp
  · rw [inv_neg, inv_one, map_neg, map_one, show (2 : ZMod 3) = -1 from rfl]
    rw [show (-1 : ZMod 3) * (u + -1) = -1 * u + 1 by ring,
      show (-1 : ZMod 3) * (u + 1) = -1 * u + -1 by ring]
    ring

end
end Dubon2026
