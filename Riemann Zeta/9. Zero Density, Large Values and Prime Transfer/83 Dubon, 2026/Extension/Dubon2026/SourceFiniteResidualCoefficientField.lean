import Dubon2026.CoefficientSubalgebraRepresentationContinuity
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! DUB-17/18 -> arithmetic automorphy -> finite residual coefficient field.
The actual continuous residual representation has finite image; adjoining
its finitely many matrix entries inside the residue algebraic closure
gives a finite field. The original matrices, group law and continuity
descend through the literal coefficient inclusion. -/
namespace Dubon2026
noncomputable section
open Matrix

theorem sourceFiniteImage_exists_finiteCoefficientField
    {G F K : Type} [Group G] [TopologicalSpace G]
    [Field F] [Finite F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [TopologicalSpace K]
    (ρ : G →* GeneralLinearGroup (Fin 2) K) (hρ : Continuous ρ)
    (hfinite : (Set.range ρ).Finite) :
    ∃ S : IntermediateField F K, Finite S ∧
      ∃ η : G →* GeneralLinearGroup (Fin 2) S, Continuous η ∧
        (GeneralLinearGroup.map S.val.toRingHom).comp η = ρ := by
  classical
  letI : Finite (Set.range ρ) := hfinite.to_subtype
  let entries : Set K := Set.range (fun x : Set.range ρ × Fin 2 × Fin 2 =>
    x.1.val.val x.2.1 x.2.2)
  haveI : Finite entries := (Set.finite_range _).to_subtype
  let S := IntermediateField.adjoin F entries
  letI : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hentry (g : G) (i j : Fin 2) : (ρ g).val i j ∈ S :=
    IntermediateField.subset_adjoin F entries ⟨⟨⟨ρ g, ⟨g, rfl⟩⟩, i, j⟩, rfl⟩
  let A (g : G) : Matrix (Fin 2) (Fin 2) S := fun i j => ⟨(ρ g).val i j, hentry g i j⟩
  have hA (g : G) : (RingHom.mapMatrix S.val.toRingHom) (A g) = (ρ g).val := rfl
  have hdet (g : G) : IsUnit (A g).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he := congrArg S.val.toRingHom hz
    rw [RingHom.map_det, hA, map_zero] at he
    exact (ρ g).det_ne_zero he
  let lift (g : G) : GeneralLinearGroup (Fin 2) S := GeneralLinearGroup.mk'' (A g) (hdet g)
  have hlift (g : G) : GeneralLinearGroup.map S.val.toRingHom (lift g) = ρ g := by
    apply Units.ext
    exact hA g
  have hinj : Function.Injective (GeneralLinearGroup.map (n := Fin 2) S.val.toRingHom) := by
    intro x y hxy
    apply GeneralLinearGroup.ext
    intro i j
    apply Subtype.ext
    exact congrArg (fun z : GeneralLinearGroup (Fin 2) K => z.val i j) hxy
  let η : G →* GeneralLinearGroup (Fin 2) S :=
    { toFun := lift
      map_one' := hinj (by rw [hlift, map_one, map_one])
      map_mul' := fun g h => hinj (by simp only [map_mul, hlift]) }
  have hmap : (GeneralLinearGroup.map S.val.toRingHom).comp η = ρ :=
    MonoidHom.ext hlift
  letI : Finite S := Module.finite_of_finite F
  refine ⟨S, inferInstance, η, ?_, hmap⟩
  apply generalLinearSubalgebra_continuous S.toSubalgebra η
  change Continuous ((GeneralLinearGroup.map S.val.toRingHom).comp η)
  rw [hmap]
  exact hρ

end
end Dubon2026
