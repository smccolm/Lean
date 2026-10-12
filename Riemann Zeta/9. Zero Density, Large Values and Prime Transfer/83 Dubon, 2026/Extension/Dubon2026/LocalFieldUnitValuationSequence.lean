import Dubon2026.LocalFieldGaloisUnitOrder
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The actual Galois-equivariant local unit valuation sequence -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The original integer-unit inclusion followed by the actual normalized
valuation onto the integers with their trivial Galois action. -/
def localFieldUnitValuationShortComplex : ShortComplex (Rep ℤ Gal(L/K)) := by
  letI := localFieldIntegerUnitMulDistribMulAction K L
  exact {
    X₁ := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    X₂ := Rep.ofAlgebraAutOnUnits K L
    X₃ := Rep.trivial ℤ Gal(L/K) ℤ
    f := Rep.ofHom ⟨(Units.map (algebraMap 𝒪[L] L).toMonoidHom).toAdditive.toIntLinearMap, by
      intro σ
      ext u
      exact congrArg Units.val
        (localFieldIntegerUnit_inclusion_equivariant K L σ (Additive.toMul u))⟩
    g := Rep.ofHom ⟨(localFieldUnitOrder L).toIntLinearMap, by
      intro σ
      ext u
      exact localFieldUnitOrder_galois_invariant K L σ (Additive.toMul u)⟩
    zero := by
      ext u
      exact (localFieldUnitOrder_eq_zero_iff_integer_unit L _).mpr
        ⟨Additive.toMul u, rfl⟩ }

/-- The original valuation sequence is short exact: injective integer-unit
inclusion, precisely its original zero-order image, and surjective integer order. -/
theorem localFieldUnitValuationShortComplex_shortExact :
    (localFieldUnitValuationShortComplex K L).ShortExact := by
  letI := localFieldIntegerUnitMulDistribMulAction K L
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr ?_
    epi_g := (Rep.epi_iff_surjective _).mpr (localFieldUnitOrder_surjective L) }
  · apply ((localFieldUnitValuationShortComplex K L).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext u
    change (∃ a : Additive 𝒪[L]ˣ,
      Additive.ofMul (Units.map (algebraMap 𝒪[L] L).toMonoidHom (Additive.toMul a)) = u) ↔
      localFieldUnitOrder L u = 0
    constructor
    · rintro ⟨a, rfl⟩
      exact (localFieldUnitOrder_eq_zero_iff_integer_unit L _).mpr ⟨a.toMul, rfl⟩
    · intro hu
      obtain ⟨a, ha⟩ := (localFieldUnitOrder_eq_zero_iff_integer_unit L u.toMul).mp hu
      exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩
  · intro u v h
    apply Additive.toMul.injective
    exact localFieldIntegerUnit_inclusion_injective L h

end
end Dubon2026
