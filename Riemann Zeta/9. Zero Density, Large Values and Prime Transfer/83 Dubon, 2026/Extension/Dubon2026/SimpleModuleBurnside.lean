import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! # The actual algebra action on a simple finite-dimensional module is surjective -/

namespace Dubon2026

noncomputable section

variable (K A V : Type*) [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [IsSimpleModule A V] [FiniteDimensional K V] [IsAlgClosed K]

/-- For the actual simple finite-dimensional module over an algebraically closed field, every original coefficient-linear endomorphism is induced by an element of the original acting algebra. -/
theorem simpleModule_algebraAction_surjective :
    Function.Surjective (Module.toModuleEnd K (S := A) V) := by
  classical
  intro f
  let f' : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro u v
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).surjective u
        change f (c • v) = c • f v
        exact f.map_smul c v }
  let b := Module.Free.chooseBasis K V
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex K V)
  let s : Finset V := Finset.univ.image b
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := V) f' s
  refine ⟨a, ?_⟩
  apply b.ext
  intro i
  exact (ha (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).symm

end
end Dubon2026
