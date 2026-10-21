import Dubon2026.SourceFiniteOrderTrace
import Dubon2026.SourceEllipticPrimeNorm
import Dubon2026.SourceIntegralHeckeConjugation

/-! DUB-17/18 -> residual Galois association -> detected finite-order
weight-two class -> exact Eisenstein Hecke eigenvalues. The actual prime
diagonal conjugate of a finite-order upper-subgroup element has the same
value under every original additive homomorphism.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). The original integral
conjugation and its proved comparison with the native Hecke map are reused.
-/

namespace Dubon2026.SourceFiniteOrder
noncomputable section
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The original small-trace matrix and its actual integral diagonal
conjugate are conjugate inside the original congruence subgroup. -/
theorem exists_mul_eq_mul_integralConj {Q ℓ : ℕ} (hℓ : ℓ.Prime)
    (k : heckeUpperSubgroup Q ℓ)
    (ht : (k.val.val 0 0 + k.val.val 1 1).natAbs ≤ 1) :
    ∃ u : SL(2, ℤ), (Q : ℤ) ∣ u 1 0 ∧
      k.val.val * u = u * (sourceIntegralHeckeConjugate k).val := by
  let δ : SL(2, ℤ) := k.val.val
  have hb : (ℓ : ℤ) ∣ δ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp k.property
  have hc : (Q : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp (Gamma0_mem.mp k.val.property)
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have ha : (ℓ : ℤ) ∣ δ 0 0 ^ 2 - (δ 0 0 + δ 1 1) * δ 0 0 + 1 :=
    ⟨-(b' * δ 1 0), by
      linear_combination (-1 : ℤ) * hdet + (-(δ 1 0)) * hb'⟩
  obtain ⟨x, y, hQ, s, hs⟩ :=
    exists_norm_eq_prime hℓ (δ 0 0 + δ 1 1) (δ 0 0) ht ha
  have hdiv : δ 0 1 / (ℓ : ℤ) = b' := by
    rw [hb']; exact Int.mul_ediv_cancel_left b' hℓ0
  have hdet' : (x + y * δ 1 1) * s - (-(y * b')) * (-(y * δ 1 0)) = 1 := by
    apply mul_left_cancel₀ hℓ0
    linear_combination hQ + y ^ 2 * hdet - (x + y * δ 1 1) * hs +
      y ^ 2 * δ 1 0 * hb'
  refine ⟨⟨!![x + y * δ 1 1, -(y * b'); -(y * δ 1 0), s],
    by rw [Matrix.det_fin_two_of]; exact hdet'⟩, ?_, ?_⟩
  · show (Q : ℤ) ∣ -(y * δ 1 0)
    rw [hc']
    exact ⟨-(y * c'), by ring⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (δ.val * !![x + y * δ 1 1, -(y * b'); -(y * δ 1 0), s]) i j =
      (!![x + y * δ 1 1, -(y * b'); -(y * δ 1 0), s] *
        !![δ 0 0, δ 0 1 / (ℓ : ℤ); δ 1 0 * (ℓ : ℤ), δ 1 1]) i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hdiv]
    · linear_combination (-(y * δ 1 0)) * hb'
    · linear_combination (-b') * hs + s * hb'
    · linear_combination (δ 1 0) * hs
    · ring

/-- The genuine diagonal Hecke conjugation preserves every additive
homomorphism value on actual finite-order upper-subgroup elements. -/
theorem hom_conjugation_eq_of_finiteOrder {Q ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    {A : Type} [AddCommGroup A] (φ : Additive (Gamma0 Q) →+ A)
    (k : heckeUpperSubgroup Q ℓ) (hk : IsOfFinOrder k.val) :
    φ (Additive.ofMul (sourceHeckeConjugation hℓ k)) = φ (Additive.ofMul k.val) := by
  have hfin : IsOfFinOrder k.val.val := Submonoid.isOfFinOrder_coe.mpr hk
  obtain ⟨n, hn, hkn⟩ := hfin.exists_pow_eq_one
  rw [← sourceIntegralHeckeConjugate_eq_prime hℓ]
  rcases offDiag_eq_zero_or_natAbs_trace_le_one k.val.val hn hkn with ⟨h01, h10⟩ | ht
  · have he : sourceIntegralHeckeConjugate k = k.val := by
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [sourceIntegralHeckeConjugate, h01, h10]
    rw [he]
  · obtain ⟨u, hu, hconj⟩ := exists_mul_eq_mul_integralConj hℓ k ht
    have hu0 : u ∈ Gamma0 Q := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mpr hu
    let Uu : Gamma0 Q := ⟨u, hu0⟩
    have he : sourceIntegralHeckeConjugate k = Uu⁻¹ * k.val * Uu := by
      apply Subtype.ext
      change (sourceIntegralHeckeConjugate k).val = u⁻¹ * k.val.val * u
      rw [mul_assoc, hconj, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [he, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel

end
end Dubon2026.SourceFiniteOrder
