import Dubon2026.ArithmeticRelativeNormalizedPrimeTotal
import Dubon2026.OriginalCanonicalSubgroupIdeleTotal

/-! # Normalize the original decomposition-subgroup class invariant

The same original local class already normalizes the local completion and
the canonical global total. Trace/coefficient naturality transfers that
normalization to the actual subgroup idele-class projection, using the
same invariants furnished by the canonical class system.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- The same actual local class has normalized local completion value and normalized image in the original subgroup idele-class H2. This proposition alone asserts no existence. -/
def OriginalLocalClassNormalization
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (localInvariant : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (invD : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
      (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
      localInvariant (originalSinglePrimeIdeleH2Lift K L w y) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ)) ∧
      invD ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) y)) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ))

/-- Existence of an injective exact-image invariant on the actual decomposition-subgroup class H2, normalized on the same original local class as its local completion value. -/
def OriginalCanonicalPrimeClassNormalization
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (localInvariant : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∃ invD : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
      (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invD ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invD.range ↔
        Nat.card (OriginalFiniteDecompositionGroup K L w) • z = 0) ∧
      OriginalLocalClassNormalization K L w localInvariant invD

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))

/-- Trace compatibility and the actual idele/class projection transfer joint local/total normalization to those same original class invariants. -/
theorem originalIdeleClass_local_normalization_of_joint_total
    (localInvariant total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (invG : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ))
    (invD : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
      (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ))
    (htotal : ∀ x : groupCohomology (originalFullIdeleRep K L) 2,
      invG ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x)
    (htrace : letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
      ∀ y : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
        (originalIdeleClassRep K L)) 2,
        invG ((subgroupCohomologyTrace (originalIdeleClassRep K L)
          (OriginalFiniteDecompositionGroup K L w) 2).hom y) = invD y)
    (hn : OriginalLocalTraceJointNormalization K L w localInvariant total) :
    OriginalLocalClassNormalization K L w localInvariant invD := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨y, hl, hg⟩ := hn
  refine ⟨y, hl, ?_⟩
  have hv := originalIdeleClass_invariant_subgroup_projection_trace K L
    (OriginalFiniteDecompositionGroup K L w) total invG invD htotal htrace
    ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
      (originalIdeleSingleFiniteRepHom K L w) y)
  have he := congrArg (fun f => f.hom y) (originalSinglePrimeIdeleH2Lift_eq_trace K L w)
  exact hv.trans ((congrArg total he.symm).trans hg)

/-- The constructed canonical class system supplies an injective exact-image decomposition invariant with the proved local normalization. -/
theorem originalIdeleClass_canonical_prime_normalization
    (localInvariant total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : OriginalCanonicalClassInvariantTraceSystem K L total)
    (hn : OriginalLocalTraceJointNormalization K L w localInvariant total) :
    OriginalCanonicalPrimeClassNormalization K L w localInvariant := by
  obtain ⟨invG, _, _, ht, hs⟩ := hc
  obtain ⟨invD, hiD, hrD, _, htr⟩ := hs (OriginalFiniteDecompositionGroup K L w)
  exact ⟨invD, hiD, hrD,
    originalIdeleClass_local_normalization_of_joint_total K L w localInvariant total invG invD ht htr hn⟩

end
end Dubon2026
