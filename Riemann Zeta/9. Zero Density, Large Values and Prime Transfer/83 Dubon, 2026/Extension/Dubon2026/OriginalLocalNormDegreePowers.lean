import Dubon2026.OriginalLocalNormUnitProducts

/-! # Actual local degree powers are norms on the original completions

For the prime-degree cyclic step in DUB-17's global norm-index upper
bound, the required powers have explicit local norm preimages: the
original base inclusion raised to the quotient of global degree by the
actual decomposition-group order. This avoids an unnecessary general
abelian local-reciprocity construction in this dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual finite-local norm of an original base unit is its decomposition-group-order power. -/
theorem originalFiniteLocalNorm_baseUnit (w : HeightOneSpectrum (𝓞 L))
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ) :
    letI := originalFinitePrimeBelow_liesOver K L w
    originalFiniteLocalNorm K L w
      (Units.map (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toMonoidHom u) =
        u ^ Fintype.card (OriginalFiniteDecompositionGroup K L w) := by
  letI := originalFinitePrimeBelow_liesOver K L w
  let f := originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w
  apply Units.ext
  apply f.injective
  have h := congrArg Units.val (originalFiniteLocalNorm_baseChange K L w (Units.map f.toMonoidHom u))
  change f (↑(originalFiniteLocalNorm K L w (Units.map f.toMonoidHom u))) = _ at h
  rw [h, Units.coe_prod, Units.val_pow_eq_pow_val, map_pow]
  calc
    (∏ τ : OriginalFiniteDecompositionGroup K L w,
        ↑(Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom
          (Units.map f.toMonoidHom u))) = ∏ _τ : OriginalFiniteDecompositionGroup K L w, f u.val := by
      apply Finset.prod_congr rfl
      intro τ _
      exact originalAdicBaseChangeMap_fixed K L (originalFinitePrimeBelow K L w) w τ.val τ.property u.val
    _ = f u.val ^ Fintype.card (OriginalFiniteDecompositionGroup K L w) := by simp

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual infinite-local norm of an original base unit is its decomposition-group-order power. -/
theorem originalInfiniteLocalNorm_baseUnit (w : InfinitePlace L)
    (u : (w.comap (algebraMap K L)).Completionˣ) :
    originalInfiniteLocalNorm K L w
      (Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom u) =
        u ^ Fintype.card (OriginalInfiniteDecompositionGroup K L w) := by
  let f := originalInfiniteCompletionBaseChange K L w
  apply Units.ext
  apply f.injective
  have h := congrArg Units.val (originalInfiniteLocalNorm_baseChange K L w (Units.map f.toMonoidHom u))
  change f (↑(originalInfiniteLocalNorm K L w (Units.map f.toMonoidHom u))) = _ at h
  rw [h, Units.coe_prod, Units.val_pow_eq_pow_val, map_pow]
  calc
    (∏ τ : OriginalInfiniteDecompositionGroup K L w,
        ↑(Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom
          (Units.map f.toMonoidHom u))) = ∏ _τ : OriginalInfiniteDecompositionGroup K L w, f u.val := by
      apply Finset.prod_congr rfl
      intro τ _
      exact originalInfiniteCompletionBaseChange_fixed K L w τ.val τ.property u.val
    _ = f u.val ^ Fintype.card (OriginalInfiniteDecompositionGroup K L w) := by simp

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every global-degree power in an original finite base completion is an actual local norm. -/
theorem originalFiniteLocalNorm_degreePower (w : HeightOneSpectrum (𝓞 L))
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ) :
    u ^ Module.finrank K L ∈ (originalFiniteLocalNorm K L w).range := by
  letI := originalFinitePrimeBelow_liesOver K L w
  have hd : Fintype.card (OriginalFiniteDecompositionGroup K L w) ∣ Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card (OriginalFiniteDecompositionGroup K L w)
  obtain ⟨m, hm⟩ := hd
  refine ⟨(Units.map (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toMonoidHom u) ^ m, ?_⟩
  rw [map_pow, originalFiniteLocalNorm_baseUnit, ← pow_mul, ← hm]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every global-degree power in an original infinite base completion is an actual local norm. -/
theorem originalInfiniteLocalNorm_degreePower (w : InfinitePlace L)
    (u : (w.comap (algebraMap K L)).Completionˣ) :
    u ^ Module.finrank K L ∈ (originalInfiniteLocalNorm K L w).range := by
  have hd : Fintype.card (OriginalInfiniteDecompositionGroup K L w) ∣ Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card (OriginalInfiniteDecompositionGroup K L w)
  obtain ⟨m, hm⟩ := hd
  refine ⟨(Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom u) ^ m, ?_⟩
  rw [map_pow, originalInfiniteLocalNorm_baseUnit, ← pow_mul, ← hm]

end
end Dubon2026
