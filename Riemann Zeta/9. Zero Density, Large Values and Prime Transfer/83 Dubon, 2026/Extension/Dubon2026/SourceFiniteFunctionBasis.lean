import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.FieldTheory.Finite.Basic

/-! The actual finite-function basis needed by character-to-weight-two reduction.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the polynomial flag on functions from ZMod p -> this basis.
Pinned Mathlib Lagrange interpolation and its monomial basis replace the
separate interpolation development in the archived residual modular proof.
-/

namespace Dubon2026
noncomputable section

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The original prime-field monomial as an actual function on ZMod p. -/
def sourceFiniteFunctionMonomial (j : ℕ) : ZMod p → F :=
  fun u => (ZMod.castHom (dvd_refl p) F u) ^ j

/-- Evaluation of actual polynomials of degree less than p on the prime field. -/
def sourceFiniteFunctionEvaluation : Polynomial.degreeLT F p →ₗ[F] (ZMod p → F) where
  toFun P u := P.val.eval (ZMod.castHom (dvd_refl p) F u)
  map_add' _ _ := funext fun _ => Polynomial.eval_add
  map_smul' _ _ := by
    ext u
    simp

/-- Pinned Lagrange interpolation proves that actual evaluation is bijective. -/
theorem sourceFiniteFunctionEvaluation_bijective :
    Function.Bijective (sourceFiniteFunctionEvaluation F p) := by
  classical
  let v := ZMod.castHom (dvd_refl p) F
  have hv : Set.InjOn v (Finset.univ : Finset (ZMod p)) := v.injective.injOn
  let e := Lagrange.funEquivDegreeLT hv
  constructor
  · intro P Q h
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
    · simpa using Polynomial.mem_degreeLT.mp P.property
    · simpa using Polynomial.mem_degreeLT.mp Q.property
    · intro u _
      exact congrFun h u
  · intro f
    let P := e.symm (fun u => f u.val)
    have hP : P.val ∈ Polynomial.degreeLT F p := by simpa using P.property
    refine ⟨⟨P.val, hP⟩, funext fun u => ?_⟩
    exact congrFun (e.apply_symm_apply (fun u => f u.val)) ⟨u, Finset.mem_univ u⟩

/-- The native interpolation equivalence for the actual finite-function coefficient space. -/
def sourceFiniteFunctionEquiv :
    Polynomial.degreeLT F p ≃ₗ[F] (ZMod p → F) :=
  LinearEquiv.ofBijective (sourceFiniteFunctionEvaluation F p)
    (sourceFiniteFunctionEvaluation_bijective F p)

/-- The actual monomials of degrees below p form a basis of all functions on ZMod p. -/
def sourceFiniteFunctionBasis : Module.Basis (Fin p) F (ZMod p → F) :=
  (Polynomial.degreeLT.basis F p).map (sourceFiniteFunctionEquiv F p)

/-- The transported native basis is literally the prime-field monomial family. -/
theorem sourceFiniteFunctionBasis_apply (i : Fin p) :
    sourceFiniteFunctionBasis F p i = sourceFiniteFunctionMonomial F p i.val := by
  funext u
  change (Polynomial.degreeLT.basis F p i).val.eval _ = _
  rw [Polynomial.degreeLT.basis_val]
  simp only [Polynomial.eval_pow, Polynomial.eval_X, sourceFiniteFunctionMonomial]

end
end Dubon2026
