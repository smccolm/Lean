import Mathlib.Algebra.Lie.UniversalEnveloping

/-! # Genuine functorial composition of universal-enveloping lifts -/

namespace Dubon2026

/-- Lifting an actual composed Lie map equals composition of its genuine enveloping lifts. -/
theorem universalEnvelopingLift_comp {R L M A : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M] [Ring A] [Algebra R A]
    (ρ : M →ₗ⁅R⁆ A) (p : L →ₗ⁅R⁆ M) :
    UniversalEnvelopingAlgebra.lift R (ρ.comp p) =
      (UniversalEnvelopingAlgebra.lift R ρ).comp
        (UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp p)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply DFunLike.ext
  intro x
  change UniversalEnvelopingAlgebra.lift R (ρ.comp p) (UniversalEnvelopingAlgebra.ι R x) =
    UniversalEnvelopingAlgebra.lift R ρ
      (UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp p)
        (UniversalEnvelopingAlgebra.ι R x))
  simp only [UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply]

end Dubon2026
