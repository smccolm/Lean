import Dubon2026.OriginalLocalKummerFixedRoot
import Dubon2026.OriginalLocalNormSplitPrime

/-! # Original splitting of a Kummer extension at local powers

The already proved local-power/fixed-root comparison makes every finite
decomposition automorphism fix a generating root. The same root-ratio
argument in the original infinite completion proves the archimedean
statement. Generation then makes both original stabilizers trivial, so
the infinite local norm is surjective. These discharge the local splitting
inputs of the simple Kummer norm correction used for DUB-17's principal
S-union-T localization equality. Outside unramifiedness remains separate.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- An original local power splits a finite prime when the actual Kummer
root generates the original extension. -/
theorem originalGeneratedKummer_finite_split
    (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hGen : IntermediateField.adjoin K {(β : L)} = ⊤)
    (hLocal : Units.map (algebraMap K ((originalFinitePrimeBelow K L w).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n).range) :
    OriginalFiniteDecompositionGroup K L w = ⊥ := by
  letI := originalFinitePrimeBelow_liesOver K L w
  have hFixed := (originalLocalKummer_power_iff_fixed K L
    (originalFinitePrimeBelow K L w) w n hn ζ hζ a β hβ).mp hLocal
  have hTop : IntermediateField.fixedField (OriginalFiniteDecompositionGroup K L w) = ⊤ := by
    apply top_unique
    rw [← hGen]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hFixed)
  rw [← IntermediateField.fixingSubgroup_fixedField (OriginalFiniteDecompositionGroup K L w),
    hTop, IntermediateField.fixingSubgroup_top]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- An original archimedean power makes the actual Kummer root fixed by
the original infinite-prime stabilizer. -/
theorem originalInfiniteKummer_fixed_of_power
    (w : InfinitePlace L) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hLocal : Units.map (algebraMap K (w.comap (algebraMap K L)).Completion).toMonoidHom a ∈
      (powMonoidHom n).range) :
    (β : L) ∈ IntermediateField.fixedField (OriginalInfiniteDecompositionGroup K L w) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let f := originalInfiniteCompletionBaseChange K L w
  let j := algebraMap L w.Completion
  let k := algebraMap K (w.comap (algebraMap K L)).Completion
  obtain ⟨y, hy⟩ := hLocal
  have hy' : (y : (w.comap (algebraMap K L)).Completion) ^ n = k (a : K) :=
    congrArg Units.val hy
  have hPow : j (β : L) ^ n = f (y : (w.comap (algebraMap K L)).Completion) ^ n := by
    calc
      j (β : L) ^ n = j (algebraMap K L (a : K)) := by rw [← map_pow, hβ]
      _ = f (k (a : K)) := (originalInfiniteCompletionBaseChange_algebraMap K L w (a : K)).symm
      _ = f ((y : (w.comap (algebraMap K L)).Completion) ^ n) := congrArg f hy'.symm
      _ = f (y : (w.comap (algebraMap K L)).Completion) ^ n := map_pow f _ _
  have hRatio : (j (β : L) / f (y : (w.comap (algebraMap K L)).Completion)) ^ n = 1 := by
    rw [div_pow, hPow, div_self]
    exact pow_ne_zero n ((map_ne_zero f).mpr y.ne_zero)
  have hRoot : IsPrimitiveRoot (j (algebraMap K L ζ)) n :=
    (hζ.map_of_injective (algebraMap K L).injective).map_of_injective j.injective
  obtain ⟨i, _, hi⟩ := hRoot.eq_pow_of_pow_eq_one hRatio
  have hImage : f (k ζ ^ i * (y : (w.comap (algebraMap K L)).Completion)) = j (β : L) := by
    rw [map_mul, map_pow, originalInfiniteCompletionBaseChange_algebraMap, hi]
    exact div_mul_cancel₀ _ ((map_ne_zero f).mpr y.ne_zero)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  apply j.injective
  have hFixed := originalInfiniteCompletionBaseChange_fixed K L w σ hσ
    (k ζ ^ i * (y : (w.comap (algebraMap K L)).Completion))
  rw [hImage] at hFixed
  exact (numberFieldGaloisArchimedeanTransport_algebraMap K L σ w w hσ (β : L)).symm.trans hFixed

omit [IsGalois K L] in
/-- An original archimedean power splits its infinite prime when the actual
Kummer root generates the original extension. -/
theorem originalGeneratedKummer_infinite_split
    (w : InfinitePlace L) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hGen : IntermediateField.adjoin K {(β : L)} = ⊤)
    (hLocal : Units.map (algebraMap K (w.comap (algebraMap K L)).Completion).toMonoidHom a ∈
      (powMonoidHom n).range) :
    OriginalInfiniteDecompositionGroup K L w = ⊥ := by
  have hFixed := originalInfiniteKummer_fixed_of_power K L w n hn ζ hζ a β hβ hLocal
  have hTop : IntermediateField.fixedField (OriginalInfiniteDecompositionGroup K L w) = ⊤ := by
    apply top_unique
    rw [← hGen]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hFixed)
  rw [← IntermediateField.fixingSubgroup_fixedField (OriginalInfiniteDecompositionGroup K L w),
    hTop, IntermediateField.fixingSubgroup_top]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Trivial original infinite decomposition makes the actual archimedean
norm surjective, through the already proved base-unit norm formula. -/
theorem originalInfiniteLocalNorm_surjective_of_split
    (w : InfinitePlace L) (hw : OriginalInfiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalInfiniteLocalNorm K L w) := by
  have hd : Fintype.card (OriginalInfiniteDecompositionGroup K L w) = 1 := by
    rw [← Nat.card_eq_fintype_card, hw]
    exact Nat.card_unique
  intro u
  refine ⟨Units.map (originalInfiniteCompletionBaseChange K L w).toMonoidHom u, ?_⟩
  rw [originalInfiniteLocalNorm_baseUnit, hd, pow_one]

end
end Dubon2026
