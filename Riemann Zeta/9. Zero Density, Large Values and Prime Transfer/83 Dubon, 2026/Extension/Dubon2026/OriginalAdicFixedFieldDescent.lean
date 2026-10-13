import Dubon2026.OriginalCompletionOrbitTrace

/-! # Descent from the actual decomposition-group fixed completion

Every element fixed by the actual prime stabilizer comes from the original
base completion. The proof uses original finite-place approximation and
trace, without importing a scalar-extension model of the adeles. This
removes the finite-place fixed-field comparison assumption in the native
idele norm quotient needed on DUB-17's global duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Every element fixed by the actual original prime stabilizer lies in the original base completion. -/
theorem originalAdicBaseChangeMap_surjective_fixed (x : w.adicCompletion L)
    (hx : ∀ (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w),
      numberFieldGaloisLocalTransport K L σ w w hσ x = x) :
    ∃ a : v.adicCompletion K, originalAdicBaseChangeMap K L v w a = x := by
  let S := originalGaloisCompletionOrbit K L w
  have hw : w ∈ S := Finset.mem_image.mpr
    ⟨1, Finset.mem_univ _, numberFieldGaloisPlaceEquiv_one K L w⟩
  let z : ∀ u : S, u.1.adicCompletion L := Pi.single ⟨w, hw⟩ x
  have ht (u : HeightOneSpectrum (𝓞 L)) (hu : u ∈ S) (σ : Gal(L/K))
      (hσ : numberFieldGaloisPlaceEquiv K L σ u = w) :
      numberFieldGaloisLocalTransport K L σ u w hσ (z ⟨u, hu⟩) =
        if u = w then x else 0 := by
    by_cases huw : u = w
    · subst u
      simp only [z, Pi.single_eq_same]
      exact hx σ hσ
    · have hne : (⟨u, hu⟩ : S) ≠ ⟨w, hw⟩ := fun h => huw (congrArg Subtype.val h)
      rw [if_neg huw]
      change numberFieldGaloisLocalTransport K L σ u w hσ
        (Pi.single (M := fun t : S => t.1.adicCompletion L) (⟨w, hw⟩ : S) x ⟨u, hu⟩) = 0
      rw [Pi.single_eq_of_ne hne, map_zero]
  let T := Finset.univ.filter (fun σ : Gal(L/K) =>
    (originalGaloisCompletionSource K L w σ).1 = w)
  have h1 : (1 : Gal(L/K)) ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
      originalGaloisCompletionSource, inv_one, numberFieldGaloisPlaceEquiv_one]
  have hm : T.card ≠ 0 := Finset.card_ne_zero.mpr ⟨1, h1⟩
  have htrace : originalCompletionOrbitTrace K L w z = (T.card : w.adicCompletion L) * x := by
    unfold originalCompletionOrbitTrace
    calc
      _ = ∑ σ : Gal(L/K), if (originalGaloisCompletionSource K L w σ).1 = w then x else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        exact ht _ (originalGaloisCompletionSource K L w σ).2 σ _
      _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const]
        exact nsmul_eq_mul T.card x
  obtain ⟨a, ha⟩ := originalCompletionOrbitTrace_mem_base K L v w z
  refine ⟨a / (T.card : v.adicCompletion K), ?_⟩
  rw [map_div₀, map_natCast, ha, htrace]
  have hmc : (T.card : w.adicCompletion L) ≠ 0 := by
    rw [← map_natCast (algebraMap L (w.adicCompletion L))]
    exact (map_ne_zero (algebraMap L (w.adicCompletion L))).mpr (Nat.cast_ne_zero.mpr hm)
  field_simp

/-- The original base-completion image is exactly the fixed set of the actual original prime stabilizer. -/
theorem originalAdicBaseChangeMap_range_iff_fixed (x : w.adicCompletion L) :
    x ∈ Set.range (originalAdicBaseChangeMap K L v w) ↔
      ∀ (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w),
        numberFieldGaloisLocalTransport K L σ w w hσ x = x := by
  constructor
  · rintro ⟨a, rfl⟩ σ hσ
    exact originalAdicBaseChangeMap_fixed K L v w σ hσ a
  · exact originalAdicBaseChangeMap_surjective_fixed K L v w x

end
end Dubon2026
