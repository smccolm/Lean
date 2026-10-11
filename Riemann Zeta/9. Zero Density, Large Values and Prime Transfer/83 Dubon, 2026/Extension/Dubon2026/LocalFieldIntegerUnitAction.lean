import Dubon2026.LocalFieldIntegerGaloisRestriction
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Algebra.Equiv

/-! # The original Galois action on actual local integer units -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- The genuine inclusion of original integer units into field units is injective. -/
theorem localFieldIntegerUnit_inclusion_injective
    (L : Type) [Field L] [ValuativeRel L] :
    Function.Injective (Units.map (algebraMap 𝒪[L] L).toMonoidHom) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun w : Lˣ => (w : L)) h

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The actual restriction of original field automorphisms acts on the
original integer units by their genuine integer-ring automorphisms. -/
@[reducible]
def localFieldIntegerUnitMulDistribMulAction : MulDistribMulAction Gal(L/K) 𝒪[L]ˣ :=
  MulDistribMulAction.compHom 𝒪[L]ˣ (localFieldIntegerGaloisEquiv K L).toMonoidHom

/-- The original integer-unit inclusion commutes with the original Galois
action, by the literal field-coefficient identity of the actual restriction. -/
theorem localFieldIntegerUnit_inclusion_equivariant (σ : Gal(L/K)) (u : 𝒪[L]ˣ) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Units.map (algebraMap 𝒪[L] L).toMonoidHom (σ • u) =
      σ • Units.map (algebraMap 𝒪[L] L).toMonoidHom u := by
  letI := localFieldIntegerUnitMulDistribMulAction K L
  apply Units.ext
  exact localFieldIntegerGaloisEquiv_apply K L σ u.val

end
end Dubon2026
