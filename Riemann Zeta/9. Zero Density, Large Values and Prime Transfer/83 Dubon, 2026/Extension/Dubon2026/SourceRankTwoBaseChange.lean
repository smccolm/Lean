import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Basic

/-! DUB-17/18 -> primitive determinant -> original Tate projector image.
Native base change and finite-product equivalences retain the literal two
Hecke coordinates, including the action of each original operator. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {K E T V : Type*} [Field K] [Field E] [CommRing T]
variable [Algebra K E] [Algebra K T] [AddCommGroup V] [Module K V]

/-- Base change of the actual two Hecke coordinates. -/
def rankTwoBaseChangeEquiv (e : V ≃ₗ[K] (Fin 2 → T)) :
    E ⊗[K] V ≃ₗ[E] (Fin 2 → E ⊗[K] T) :=
  (e.baseChange K E V (Fin 2 → T)).trans (TensorProduct.piRight K E E (fun _ : Fin 2 => T))

theorem rankTwoBaseChangeEquiv_tmul (e : V ≃ₗ[K] (Fin 2 → T))
    (a : E) (v : V) (i : Fin 2) :
    rankTwoBaseChangeEquiv (E := E) e (a ⊗ₜ[K] v) i = a ⊗ₜ[K] e v i := rfl

theorem rankTwoBaseChangeEquiv_operator (e : V ≃ₗ[K] (Fin 2 → T))
    (H : Module.End K V) (t : T)
    (hH : ∀ v : V, e (H v) = fun i => t * e v i)
    (x : E ⊗[K] V) (i : Fin 2) :
    rankTwoBaseChangeEquiv e (H.baseChange E x) i =
      ((1 : E) ⊗ₜ[K] t) * rankTwoBaseChangeEquiv e x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    simp only [LinearMap.baseChange_tmul, rankTwoBaseChangeEquiv_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hH]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add]

end
end Dubon2026
