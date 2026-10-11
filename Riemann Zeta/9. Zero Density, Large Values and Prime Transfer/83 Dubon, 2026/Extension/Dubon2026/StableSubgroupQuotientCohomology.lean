import Dubon2026.StableSubgroupCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The actual subgroup quotient sequence and its cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory

attribute [local instance 1100] Rep.hV2

variable (G U : Type) [Group G] [CommGroup U] [MulDistribMulAction G U]
  (S : Subgroup U) (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S)

/-- The original subgroup, viewed as an integer submodule of the same units. -/
def stableSubgroupIntSubmodule : Submodule ℤ (Rep.ofMulDistribMulAction G U) :=
  S.toAddSubgroup.toIntSubmodule

include hS in
/-- The original restricted action preserves the same integer submodule. -/
theorem stableSubgroupIntSubmodule_stable (g : G) :
    stableSubgroupIntSubmodule G U S ≤
      (stableSubgroupIntSubmodule G U S).comap ((Rep.ofMulDistribMulAction G U).ρ g) := by
  intro u hu
  exact hS g u hu

/-- The quotient by the actual invariant subgroup, retaining the original action. -/
def stableSubgroupQuotientRep : Rep ℤ G :=
  (Rep.ofMulDistribMulAction G U).quotient (stableSubgroupIntSubmodule G U S)
    (stableSubgroupIntSubmodule_stable G U S hS)

/-- The genuine inclusion and quotient maps on the original coefficient groups. -/
def stableSubgroupShortComplex : ShortComplex (Rep ℤ G) := by
  letI := stableSubgroupMulDistribMulAction G U S hS
  exact {
    X₁ := Rep.ofMulDistribMulAction G S
    X₂ := Rep.ofMulDistribMulAction G U
    X₃ := stableSubgroupQuotientRep G U S hS
    f := Rep.ofHom ⟨S.subtype.toAdditive.toIntLinearMap, fun _ => rfl⟩
    g := (Rep.ofMulDistribMulAction G U).mkQ (stableSubgroupIntSubmodule G U S)
      (stableSubgroupIntSubmodule_stable G U S hS)
    zero := by
      ext x
      change (Submodule.Quotient.mk (Additive.ofMul ((Additive.toMul x : S) : U)) :
        (Rep.ofMulDistribMulAction G U) ⧸ stableSubgroupIntSubmodule G U S) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Additive.toMul x).property }

/-- Exactness follows from the literal subgroup inclusion and quotient kernel. -/
theorem stableSubgroupShortComplex_shortExact :
    (stableSubgroupShortComplex G U S hS).ShortExact := by
  letI := stableSubgroupMulDistribMulAction G U S hS
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr ?_
    epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
  · apply ((stableSubgroupShortComplex G U S hS).exact_map_iff_of_faithful
      (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range S.subtype.toAdditive.toIntLinearMap =
      LinearMap.ker (stableSubgroupIntSubmodule G U S).mkQ
    rw [Submodule.ker_mkQ]
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact (Additive.toMul v).property
    · intro hu
      exact ⟨Additive.ofMul (⟨Additive.toMul u, hu⟩ : S), rfl⟩
  · intro u v h
    exact Additive.toMul.injective (Subtype.ext h)

/-- Finiteness of the original multiplicative quotient is unchanged by
viewing the same groups additively as the actual quotient representation. -/
theorem stableSubgroupQuotientRep_finite [Finite (U ⧸ S)] :
    Finite (stableSubgroupQuotientRep G U S hS) := by
  change Finite (U ⧸ S)
  infer_instance

/-- The original quotient map induces an isomorphism in degree n when the
two adjacent cohomology groups of the actual kernel subgroup vanish. -/
theorem stableSubgroupQuotient_cohomology_isIso (n : ℕ)
    (hn : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) n))
    (hs : letI := stableSubgroupMulDistribMulAction G U S hS
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G S) (n + 1))) :
    IsIso ((groupCohomology.functor ℤ G n).map
      (stableSubgroupShortComplex G U S hS).g) := by
  let X := stableSubgroupShortComplex G U S hS
  have hX := stableSubgroupShortComplex_shortExact G U S hS
  haveI : Mono ((groupCohomology.functor ℤ G n).map X.g) :=
    (groupCohomology.mapShortComplex₂_exact hX n).mono_g (hn.eq_of_src _ _)
  haveI : Epi ((groupCohomology.functor ℤ G n).map X.g) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := n) (j := n + 1) rfl).epi_f
      (hs.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end
end Dubon2026
