import Dubon2026.ArithmeticSUnitIdeleBaseChange

/-! # Original Kummer correction of full ideles at fixed support

An actual root of a principal correction removes the outside valuations of
the original base-changed idele. This gives a supported representative,
without enlarging S, for the q-torsion class comparison in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hST in
/-- The actual original root correction makes the base-changed idele supported at precisely the original pulled-back support. -/
theorem originalIdele_rootCorrection_mem_supported
    (q : ℕ) (hq : 0 < q) (x : (AdeleRing (𝓞 K) K)ˣ) (u : Kˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      v.valuation K (u : K) = Valued.v (numberFieldIdeleFiniteComponent K v x).val ^ q)
    (β : Lˣ) (hβ : (β : L) ^ q = algebraMap K L (u : K)) :
    originalIdeleBaseChangeMap K L x / numberFieldPrincipalIdele L β ∈
      numberFieldSupportedIdeles L T := by
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  intro w hw
  let v := originalFinitePrimeBelow K L w
  letI := originalFinitePrimeBelow_liesOver K L w
  have hv : v ∉ S := fun h => hw ((hST w).mpr h)
  have hroot := congrArg (w.valuation L) hβ
  rw [map_pow, original_valuation_algebraMap_pow K L v w, hu v hv] at hroot
  have hp : Valued.v (numberFieldIdeleFiniteComponent L w (numberFieldPrincipalIdele L β)).val =
      w.valuation L (β : L) := by
    change Valued.v (algebraMap L (w.adicCompletion L) β.val) = _
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
    rfl
  rw [map_div, Units.val_div_eq_div_val, map_div₀, hp]
  change Valued.v (originalAdicBaseChangeMap K L v w
    (numberFieldIdeleFiniteComponent K v x).val) / w.valuation L (β : L) = 1
  rw [originalAdicBaseChangeMap_valuation]
  apply (pow_eq_one_iff_of_nonneg zero_le hq.ne').mp
  rw [div_pow, hroot, ← pow_mul, ← pow_mul, Nat.mul_comm, div_self]
  simp

end
end Dubon2026
