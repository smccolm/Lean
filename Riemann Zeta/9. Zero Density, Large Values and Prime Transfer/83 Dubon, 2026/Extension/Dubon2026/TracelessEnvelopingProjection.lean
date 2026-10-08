import Dubon2026.ComplexTracelessProjection
import Dubon2026.UniversalEnvelopingInduction
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # The actual full GL₂ enveloping center projects to the genuine SL₂ center -/

namespace Dubon2026

noncomputable section

/-- Lift the genuine original trace projection to the actual universal enveloping algebras. -/
def tracelessEnvelopingProjection :
    UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) →ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ ComplexSl2 :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp complexTracelessProjection)

/-- The actual enveloping projection retains the exact original trace projection on every matrix generator. -/
theorem tracelessEnvelopingProjection_generator (a : Matrix (Fin 2) (Fin 2) ℂ) :
    tracelessEnvelopingProjection (UniversalEnvelopingAlgebra.ι ℂ a) =
      UniversalEnvelopingAlgebra.ι ℂ (complexTracelessProjection a) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ a

/-- The genuine enveloping projection is surjective onto the entire original SL₂ enveloping algebra. -/
theorem tracelessEnvelopingProjection_surjective : Function.Surjective tracelessEnvelopingProjection := by
  intro z
  induction z using universalEnveloping_induction with
  | hscalar c => exact ⟨algebraMap ℂ _ c, tracelessEnvelopingProjection.commutes c⟩
  | hgenerator x =>
      refine ⟨UniversalEnvelopingAlgebra.ι ℂ x.val, ?_⟩
      rw [tracelessEnvelopingProjection_generator, complexTracelessProjection_sl]
  | hadd x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  | hmul x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

/-- Every original full GL₂ central element projects to the actual SL₂ center by genuine surjectivity. -/
theorem tracelessEnvelopingProjection_mem_center
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ))) :
    tracelessEnvelopingProjection z.val ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) := by
  rw [Subalgebra.mem_center_iff]
  intro w
  obtain ⟨a, rfl⟩ := tracelessEnvelopingProjection_surjective w
  exact ((show Commute a z.val from Subalgebra.mem_center_iff.mp z.property a).map
    tracelessEnvelopingProjection).eq

/-- The actual trace projection therefore gives a genuine algebra map of the original full enveloping centers. -/
def tracelessEnvelopingCenterProjection :
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) →ₐ[ℂ]
      Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) where
  toFun z := ⟨tracelessEnvelopingProjection z.val, tracelessEnvelopingProjection_mem_center z⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' z w := Subtype.ext (map_mul _ z.val w.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ z.val w.val)
  commutes' c := Subtype.ext (tracelessEnvelopingProjection.commutes c)

end
end Dubon2026
