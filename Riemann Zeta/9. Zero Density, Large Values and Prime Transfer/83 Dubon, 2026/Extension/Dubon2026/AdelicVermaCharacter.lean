import Dubon2026.AdelicVermaMap
import Dubon2026.AdelicInfinitesimalCharacter
import Dubon2026.VermaCentralReflection
import Dubon2026.EnvelopingIntertwiner

/-! # Exact full central-character comparison for the original cusp module -/

namespace Dubon2026

noncomputable section
open Polynomial Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Polynomial evaluation on the original cusp generator intertwines the full genuine enveloping action. -/
theorem adelicVermaMap_enveloping (hf : f ≠ 0)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (p : ℂ[X]) :
    adelicVermaMap f (vermaPolynomialEnvelopingAction (-(k : ℂ)) z p) =
      adelicEnvelopingAction f z (adelicVermaMap f p) := by
  apply universalEnveloping_intertwine (vermaPolynomialEnvelopingAction (-(k : ℂ)))
    (adelicEnvelopingAction f) (adelicVermaMap f) _ z p
  intro x q
  exact (congrArg (fun T : Module.End ℂ ℂ[X] => adelicVermaMap f (T q))
    (vermaPolynomialEnvelopingAction_generator (-(k : ℂ)) x)).trans
    ((adelicVermaMap_matrix f hf x q).trans
      (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) => T (adelicVermaMap f q))
        (adelicEnvelopingAction_generator f x)).symm)

/-- Every actual central scalar of the original cusp module equals the original Verma scalar at -k. -/
theorem adelicInfinitesimalCharacter_eq_verma (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    adelicInfinitesimalCharacter f hf z = vermaPolynomialCentralValue (-(k : ℂ)) z := by
  have hv : adelicVermaMap f 1 ≠ 0 := by
    intro h
    exact adelicCyclicHilbertGenerator_ne_zero f hf
      (congrArg Subtype.val ((adelicVermaMap_one f).symm.trans h))
  have hs : adelicEnvelopingAction f z.val (adelicVermaMap f 1) =
      adelicInfinitesimalCharacter f hf z • adelicVermaMap f 1 :=
    (congrArg (adelicEnvelopingAction f z.val) (adelicVermaMap_one f)).trans
      ((adelicInfinitesimalCharacter_generator f hf z).trans
        (congrArg (fun v : adelicRealSmoothSubmodule f => adelicInfinitesimalCharacter f hf z • v)
          (adelicVermaMap_one f)).symm)
  exact (linearIntertwiner_eigenvalue
    (vermaPolynomialEnvelopingAction (-(k : ℂ)) z.val) (adelicEnvelopingAction f z.val)
    (adelicVermaMap f) 1 _ _ hv (adelicVermaMap_enveloping f hf z.val 1)
    (vermaPolynomialCentralValue_generator (-(k : ℂ)) z) hs).symm

/-- The entire genuine infinitesimal character of the original cusp module has the reflected algebraic parameter k-2. -/
theorem adelicInfinitesimalCharacter_eq_reflected_verma (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    adelicInfinitesimalCharacter f hf z = vermaPolynomialCentralValue ((k : ℂ) - 2) z :=
  (adelicInfinitesimalCharacter_eq_verma f hf z).trans
    (vermaPolynomialCentralValue_cusp_reflection k z)

/-- The same original universal central polynomial evaluates to the actual cusp-module character at k-2. -/
theorem adelicInfinitesimalCharacter_polynomial (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    adelicInfinitesimalCharacter f hf z =
      aeval ((k : ℂ) - 2) (vermaUniversalCentralPolynomial z) :=
  (adelicInfinitesimalCharacter_eq_reflected_verma f hf z).trans
    (vermaUniversalCentralPolynomial_aeval ((k : ℂ) - 2) z).symm

end
end Dubon2026
