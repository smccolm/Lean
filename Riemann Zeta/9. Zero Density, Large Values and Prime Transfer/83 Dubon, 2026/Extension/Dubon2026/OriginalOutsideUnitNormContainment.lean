import Dubon2026.OriginalUnramifiedUnitNormGeneral
import Dubon2026.OriginalIdeleNormLocalGlobal
import Dubon2026.OriginalIdeleClassNativeNormQuotient
import Dubon2026.OriginalOutsideClassExactSequence

/-! # Actual outside units are norms without global cyclicity

The original supported-coordinate inclusion is one at infinity and at the
selected finite primes. Its remaining coordinates are integer units, so
the existing local-to-global norm assembly applies after deriving local
cyclicity from unramifiedness. This is the outside-unit containment needed
for the S-unit Kummer norm field in DUB-17's invariant norm-root chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual outside-unit idele has a full original norm preimage when
every upper prime outside the prescribed support is absolutely unramified. -/
theorem originalOutsideSupportedInclusion_is_norm
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (u : supportedOutsideUnitRep K K S hS) :
    ∃ b : (AdeleRing (𝓞 L) L)ˣ, originalIdeleNorm K L b =
      ((originalOutsideSupportedInclusion K K S hS).hom u).toMul.val := by
  let a := (originalOutsideSupportedInclusion K K S hS).hom u
  have ha : supportedIdeleLocalFactorLinearEquiv K S a = (0, u) :=
    (supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply (0, u)
  apply originalIdeleNorm_exists_of_local K L a.toMul.val
  · intro w
    let v := originalFinitePrimeBelow K L w
    by_cases hv : v ∈ S
    · have he := congrArg (fun z => z.1 (Sum.inr (⟨v, hv⟩ : S))) ha
      change Additive.ofMul (numberFieldIdeleFiniteComponent K v a.toMul.val) = 0 at he
      have hone : numberFieldIdeleFiniteComponent K v a.toMul.val = 1 :=
        congrArg Additive.toMul he
      rw [hone]
      exact (originalFiniteLocalNorm K L w).range.one_mem
    · have hu : numberFieldIdeleFiniteComponent K v a.toMul.val ∈
          (v.adicCompletionIntegers K).units := by
        have h := a.toMul.property
        simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at h
        exact h v hv
      exact originalFiniteLocalNorm_integerUnit_of_unramified_general K L w
        (hAway w hv) _ hu
  · intro w
    have he := congrArg (fun z => z.1 (Sum.inl (w.comap (algebraMap K L)))) ha
    change Additive.ofMul
      (numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a.toMul.val) = 0 at he
    have hone : numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a.toMul.val = 1 :=
      congrArg Additive.toMul he
    rw [hone]
    exact (originalInfiniteLocalNorm K L w).range.one_mem

/-- The literal original outside-unit class range lies in the actual
field-norm range, also for noncyclic Galois extensions. -/
theorem originalOutsideIdeleClass_range_le_norm
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap ≤
      LinearMap.range (originalIdeleClassNormLinear K L) := by
  rintro x ⟨u, rfl⟩
  obtain ⟨b, hb⟩ := originalOutsideSupportedInclusion_is_norm K L S hS hAway u
  refine ⟨Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range b), ?_⟩
  change Additive.ofMul (originalIdeleClassNorm K L
    (QuotientGroup.mk' (numberFieldPrincipalIdele L).range b)) = _
  rw [originalIdeleClassNorm_mk, hb]
  rfl

end
end Dubon2026
