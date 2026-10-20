import Dubon2026.GeneralLinearRegularTranslation
import Dubon2026.GeneralLinearBorelCharacter
import Mathlib.RepresentationTheory.Subrepresentation

/-! Geraghty Definition 2.2.1's literal integral algebraic induction:
regular functions satisfying f(bg) = (w0(lam))(b) f(g) over every
coefficient algebra, with the source right-translation action. Closure
and invariance are proved. Finite freeness is proved in IntegralInducedFiniteFree;
the highest-weight identification remains a separate obligation. -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] (n : ℕ) (lam : Fin n → ℤ)

/-- The exact source induced module consists of original regular functions with the original reversed-weight Borel covariance over every coefficient algebra. -/
def generalLinearIntegralInducedSubmodule : Submodule R (GeneralLinearRegularFunctions R n) where
  carrier p := ∀ (A : Type u) [CommRing A] [Algebra R A]
    (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
      generalLinearRegularEval (b.val * g) p =
        (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g p
  zero_mem' := by
    intro A _ _ g b
    simp
  add_mem' {p q} hp hq := by
    intro A _ _ g b
    simp only [map_add, hp A g b, hq A g b, mul_add]
  smul_mem' a p hp := by
    intro A _ _ g b
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes, hp A g b]
    ring

/-- The source defining covariance is stated on the actual regular functions and every original coefficient algebra. -/
theorem generalLinearIntegralInducedSubmodule_mem (p : GeneralLinearRegularFunctions R n) :
    p ∈ generalLinearIntegralInducedSubmodule R n lam ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A]
        (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        generalLinearRegularEval (b.val * g) p =
          (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g p := Iff.rfl

/-- The original right-translation action preserves the exact source Borel covariance over every coefficient algebra. -/
theorem generalLinearIntegralInducedSubmodule_stable
    (x : GeneralLinearGroup (Fin n) R) {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam) :
    generalLinearRegularRightTranslate x p ∈ generalLinearIntegralInducedSubmodule R n lam := by
  intro A _ _ g b
  have hbg := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate x (b.val * g)) p
  have hg := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate x g) p
  change generalLinearRegularEval (b.val * g) (generalLinearRegularRightTranslate x p) = _
  rw [show generalLinearRegularEval (b.val * g) (generalLinearRegularRightTranslate x p) =
    generalLinearRegularEval ((b.val * g) * GeneralLinearGroup.map (algebraMap R A) x) p from hbg]
  rw [show generalLinearRegularEval g (generalLinearRegularRightTranslate x p) =
    generalLinearRegularEval (g * GeneralLinearGroup.map (algebraMap R A) x) p from hg]
  rw [mul_assoc]
  exact hp A (g * GeneralLinearGroup.map (algebraMap R A) x) b

/-- The actual integral algebraic induction is a genuine subrepresentation of the original regular-function action. -/
def generalLinearIntegralInduced :
    Subrepresentation (generalLinearRegularRepresentation (R := R) (n := n)) where
  toSubmodule := generalLinearIntegralInducedSubmodule R n lam
  apply_mem_toSubmodule := generalLinearIntegralInducedSubmodule_stable R n lam

/-- The source integral coefficient representation, on the actual induced module with its original right-translation action. -/
def generalLinearIntegralInducedRepresentation :
    Representation R (GeneralLinearGroup (Fin n) R) (generalLinearIntegralInducedSubmodule R n lam) :=
  (generalLinearIntegralInduced R n lam).toRepresentation

/-- Evaluation of the induced action has the exact source f(gx) formula on the same regular function. -/
theorem generalLinearIntegralInducedRepresentation_eval
    (x : GeneralLinearGroup (Fin n) R) (p : generalLinearIntegralInducedSubmodule R n lam)
    (A : Type u) [CommRing A] [Algebra R A] (g : GeneralLinearGroup (Fin n) A) :
    generalLinearRegularEval g (generalLinearIntegralInducedRepresentation R n lam x p).val =
      generalLinearRegularEval (g * GeneralLinearGroup.map (algebraMap R A) x) p.val :=
  AlgHom.congr_fun (generalLinearRegularEval_rightTranslate x g) p.val

end
end Dubon2026
