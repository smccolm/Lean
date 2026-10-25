import Dubon2026.SourceOriginalNormEvaluation
import Dubon2026.SourceOriginalPicardGroup

/-! DUB-17/18 -> Hecke-adjoint original Weil pairing. Specialize the
existing actual Picard pullback and norm maps to a specified map of
original modular function fields. Native finiteness and residue theorems
discharge every geometric premise, including on torsion. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M]

/-- The existing finite Picard pullback along an original field embedding. -/
def originalPicardPullback
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L) :
    Pic0 L (modularFunctionFieldOver N L) →+ Pic0 L (modularFunctionFieldOver M L) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  exact Pic0.finitePullback (modularFunctionFieldOver M L)
    (original_place_residue_algebraMap_bijective N L) (original_place_residue_algebraMap_bijective M L)

/-- The existing finite Picard norm along an original field embedding. -/
def originalPicardNorm
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L) :
    Pic0 L (modularFunctionFieldOver M L) →+ Pic0 L (modularFunctionFieldOver N L) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  exact Pic0.geometricPushforward (modularFunctionFieldOver N L)
    (original_place_residue_algebraMap_bijective N L) (original_place_residue_algebraMap_bijective M L)

theorem originalPicardPullback_mk
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L)) :
    originalPicardPullback L N M φ (Pic0.mk D) = Pic0.mk
      ⟨Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val,
        Divisor.finitePullbackAlong_mem_degZero φ _
          (original_place_residue_algebraMap_bijective N L)
          (original_place_residue_algebraMap_bijective M L) D.property⟩ := rfl

theorem originalPicardNorm_mk
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver M L)) :
    originalPicardNorm L N M φ (Pic0.mk D) = Pic0.mk
      ⟨Divisor.geometricPushforwardAlong φ (original_field_hom_finite L N M φ) D.val,
        Divisor.geometricPushforwardAlong_mem_degZero φ _
          (original_place_residue_algebraMap_bijective N L)
          (original_place_residue_algebraMap_bijective M L) D.property⟩ := rfl

private def torsionMap {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] (a : Pic0 K F →+ Pic0 K E) (n : ℕ) :
    Pic0.torsion (K := K) (F := F) n →+ Pic0.torsion (K := K) (F := E) n where
  toFun x := ⟨a x.val, by
    rw [Pic0.mem_torsion_iff, ← map_nsmul, Pic0.mem_torsion_iff.mp x.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero a)
  map_add' x y := Subtype.ext (map_add a x.val y.val)

/-- Pullback on the actual original Picard torsion subgroups. -/
def originalPicardPullbackTorsion
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L) (n : ℕ) :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver M L) n :=
  torsionMap (originalPicardPullback L N M φ) n

/-- Norm on the actual original Picard torsion subgroups. -/
def originalPicardNormTorsion
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L) (n : ℕ) :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver M L) n →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n :=
  torsionMap (originalPicardNorm L N M φ) n

end
end Dubon2026.SourceFunctionField
