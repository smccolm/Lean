import Dubon2026.OriginalInfiniteAdeleFixedDescent

/-! # Actual original archimedean fixed-field descent

An original infinite adele supported at one place has actual Galois trace
equal there to the nonzero stabilizer count times a fixed local element.
Existing infinite-adele trace descent therefore constructs its original
base-completion preimage. This is the archimedean fixed-field comparison
needed for local norm formulas in DUB-17's norm-index/reciprocity chain.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (w : InfinitePlace L)

/-- The original base completion is fixed by the actual original archimedean decomposition action. -/
theorem originalInfiniteCompletionBaseChange_fixed (σ : Gal(L/K)) (hσ : σ • w = w)
    (x : (w.comap (algebraMap K L)).Completion) :
    numberFieldGaloisArchimedeanTransport K L σ w w hσ
      (originalInfiniteCompletionBaseChange K L w x) = originalInfiniteCompletionBaseChange K L w x := by
  let b : InfiniteAdeleRing K := Pi.single (w.comap (algebraMap K L)) x
  have hb : originalInfiniteAdeleBaseChangeMap K L b w = originalInfiniteCompletionBaseChange K L w x := by
    change originalInfiniteCompletionBaseChange K L w (Pi.single _ x _) = _
    rw [Pi.single_eq_same]
  have h := congrArg (fun a : InfiniteAdeleRing L => a w) (originalInfiniteAdeleBaseChangeMap_fixed K L σ b)
  change numberFieldInfiniteAdeleGaloisMap K L σ (originalInfiniteAdeleBaseChangeMap K L b) w = originalInfiniteAdeleBaseChangeMap K L b w at h
  rw [numberFieldInfiniteAdeleGaloisMap_apply K L σ _ w w hσ, hb] at h
  exact h

variable [FiniteDimensional K L] [IsGalois K L]

/-- Every element fixed by the actual original archimedean prime stabilizer descends to the actual base completion. -/
theorem originalInfiniteCompletionBaseChange_surjective_fixed (x : w.Completion)
    (hx : ∀ (σ : Gal(L/K)) (hσ : σ • w = w), numberFieldGaloisArchimedeanTransport K L σ w w hσ x = x) :
    ∃ a : (w.comap (algebraMap K L)).Completion, originalInfiniteCompletionBaseChange K L w a = x := by
  let z : InfiniteAdeleRing L := Pi.single w x
  have ht (u : InfinitePlace L) (σ : Gal(L/K)) (hσ : σ • u = w) :
      numberFieldGaloisArchimedeanTransport K L σ u w hσ (z u) = if u = w then x else 0 := by
    by_cases huw : u = w
    · subst u
      simp only [z, Pi.single_eq_same]
      exact hx σ hσ
    · rw [if_neg huw]
      change numberFieldGaloisArchimedeanTransport K L σ u w hσ
        (Pi.single (M := fun t : InfinitePlace L => t.Completion) w x u) = 0
      rw [Pi.single_eq_of_ne huw, map_zero]
  let T := Finset.univ.filter (fun σ : Gal(L/K) => σ⁻¹ • w = w)
  have h1 : (1 : Gal(L/K)) ∈ T := by simp only [T, Finset.mem_filter, Finset.mem_univ, inv_one, one_smul, and_self]
  have hm : T.card ≠ 0 := Finset.card_ne_zero.mpr ⟨1, h1⟩
  have htrace : (∑ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ z) w = (T.card : w.Completion) * x := by
    let ev : InfiniteAdeleRing L →+ w.Completion := {
      toFun a := a w
      map_zero' := rfl
      map_add' _ _ := rfl }
    have heval : (∑ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ z) w =
        ∑ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ z w := map_sum ev _ _
    rw [heval]
    calc
      _ = ∑ σ : Gal(L/K), if σ⁻¹ • w = w then x else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        exact ht (σ⁻¹ • w) σ (smul_inv_smul σ w)
      _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const]
        exact nsmul_eq_mul T.card x
  obtain ⟨b, hb⟩ := originalInfiniteAdeleTrace_mem_base K L z
  refine ⟨b (w.comap (algebraMap K L)) / (T.card : (w.comap (algebraMap K L)).Completion), ?_⟩
  have hc := congrArg (fun a : InfiniteAdeleRing L => a w) hb
  change originalInfiniteCompletionBaseChange K L w (b (w.comap (algebraMap K L))) =
    (∑ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ z) w at hc
  rw [map_div₀, map_natCast, hc, htrace]
  have hmc : (T.card : w.Completion) ≠ 0 := by
    rw [← map_natCast (algebraMap L w.Completion)]
    exact (map_ne_zero (algebraMap L w.Completion)).mpr (Nat.cast_ne_zero.mpr hm)
  field_simp

/-- The actual original base archimedean image is exactly the fixed set of the actual original prime stabilizer. -/
theorem originalInfiniteCompletionBaseChange_range_iff_fixed (x : w.Completion) :
    x ∈ Set.range (originalInfiniteCompletionBaseChange K L w) ↔
      ∀ (σ : Gal(L/K)) (hσ : σ • w = w), numberFieldGaloisArchimedeanTransport K L σ w w hσ x = x := by
  constructor
  · rintro ⟨a, rfl⟩ σ hσ
    exact originalInfiniteCompletionBaseChange_fixed K L w σ hσ a
  · exact originalInfiniteCompletionBaseChange_surjective_fixed K L w x

end
end Dubon2026
