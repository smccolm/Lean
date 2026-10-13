import Dubon2026.OriginalAdicDecompositionAction
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Actual local powers and actual Kummer decomposition fixed roots

An original Kummer radicand is a power in the original base completion
exactly when its original upper-field root is fixed by the actual prime
stabilizer. The proof uses the already proved original completed fixed-field
descent and the primitive root in the original base field. This is the
localization bridge needed to use the selected coordinate primes on DUB-17's
S-unit radical and principal/class index chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The actual local power condition is equivalent to fixation of the actual
Kummer root by the original finite decomposition group. -/
theorem originalLocalKummer_power_iff_fixed
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ n = algebraMap K L (a : K)) :
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range ↔
    (β : L) ∈ IntermediateField.fixedField (OriginalFiniteDecompositionGroup K L w) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let f := originalAdicBaseChangeMap K L v w
  let j := algebraMap L (w.adicCompletion L)
  let k := algebraMap K (v.adicCompletion K)
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (y : v.adicCompletion K) ^ n = k (a : K) :=
      congrArg Units.val hy
    have hPow : j (β : L) ^ n = f (y : v.adicCompletion K) ^ n := by
      calc
        j (β : L) ^ n = j (algebraMap K L (a : K)) := by rw [← map_pow, hβ]
        _ = f (k (a : K)) := (originalAdicBaseChangeMap_algebraMap K L v w (a : K)).symm
        _ = f ((y : v.adicCompletion K) ^ n) := congrArg f hy'.symm
        _ = f (y : v.adicCompletion K) ^ n := map_pow f _ _
    have hRatio : (j (β : L) / f (y : v.adicCompletion K)) ^ n = 1 := by
      rw [div_pow, hPow, div_self]
      exact pow_ne_zero n ((map_ne_zero f).mpr y.ne_zero)
    have hRoot : IsPrimitiveRoot (j (algebraMap K L ζ)) n :=
      (hζ.map_of_injective (algebraMap K L).injective).map_of_injective j.injective
    obtain ⟨i, _, hi⟩ := hRoot.eq_pow_of_pow_eq_one hRatio
    have hImage : f (k ζ ^ i * (y : v.adicCompletion K)) = j (β : L) := by
      rw [map_mul, map_pow, originalAdicBaseChangeMap_algebraMap, hi]
      exact div_mul_cancel₀ _ ((map_ne_zero f).mpr y.ne_zero)
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    apply j.injective
    have hFixed := originalAdicBaseChangeMap_fixed K L v w σ hσ
      (k ζ ^ i * (y : v.adicCompletion K))
    rw [hImage] at hFixed
    exact (numberFieldGaloisLocalTransport_algebraMap K L σ w w hσ (β : L)).symm.trans hFixed
  · intro hFixed
    rw [IntermediateField.mem_fixedField_iff] at hFixed
    obtain ⟨y, hy⟩ := originalAdicBaseChangeMap_surjective_fixed K L v w (j (β : L)) (by
      intro σ hσ
      rw [numberFieldGaloisLocalTransport_algebraMap]
      exact congrArg j (hFixed σ hσ))
    have hy0 : y ≠ 0 := by
      intro hz
      have h : j (β : L) = 0 := by rw [← hy, hz, map_zero]
      exact β.ne_zero ((map_eq_zero j).mp h)
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    change y ^ n = k (a : K)
    apply f.injective
    rw [map_pow, hy, ← map_pow, hβ]
    exact (originalAdicBaseChangeMap_algebraMap K L v w (a : K)).symm

end
end Dubon2026
