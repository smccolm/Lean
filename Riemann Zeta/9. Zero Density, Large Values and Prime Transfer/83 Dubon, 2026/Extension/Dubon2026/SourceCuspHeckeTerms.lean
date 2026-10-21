import Dubon2026.SourceCuspPrimeOrbits
import Dubon2026.SourceIntegralHeckeConjugation

/-! DUB-17/18 -> residual Galois association -> boundary characters of the
original complex weight-two class -> the full cusp Hecke sum. The two
actual orbit terms are computed using the already proved original integral
Hecke conjugation, with its exact original sign and normalization.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) {A : Type} [AddCommGroup A]

/-- The actual original Hecke-conjugation contribution at an upper-subgroup element. -/
def termOf (φ : Additive (Gamma0 N) →+ A) (x : Gamma0 N)
    (hx : x ∈ heckeUpperSubgroup N ℓ) : A :=
  φ (Additive.ofMul (sourceHeckeConjugation hℓ ⟨x, hx⟩))

/-- Equal original upper-subgroup elements have equal actual Hecke contributions. -/
theorem termOf_congr (φ : Additive (Gamma0 N) →+ A) {x y : Gamma0 N}
    (hx : x ∈ heckeUpperSubgroup N ℓ) (hy : y ∈ heckeUpperSubgroup N ℓ)
    (h : x = y) : termOf hℓ φ x hx = termOf hℓ φ y hy := by subst y; rfl

/-- Conjugation inside the original upper Hecke subgroup preserves its
actual contribution to an abelian homomorphism. -/
theorem termOf_conj (φ : Additive (Gamma0 N) →+ A) {x r : Gamma0 N}
    (hx : x ∈ heckeUpperSubgroup N ℓ) (hr : r ∈ heckeUpperSubgroup N ℓ)
    (hm : r⁻¹ * x * r ∈ heckeUpperSubgroup N ℓ) :
    termOf hℓ φ (r⁻¹ * x * r) hm = termOf hℓ φ x hx := by
  have he : (⟨r⁻¹ * x * r, hm⟩ : heckeUpperSubgroup N ℓ) =
      (⟨r, hr⟩ : heckeUpperSubgroup N ℓ)⁻¹ * ⟨x, hx⟩ * ⟨r, hr⟩ := rfl
  unfold termOf
  rw [he, (sourceHeckeConjugation hℓ).map_mul,
    (sourceHeckeConjugation hℓ).map_mul, (sourceHeckeConjugation hℓ).map_inv]
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
  abel

omit [NeZero ℓ] in
private theorem integralConjugate_entries (g : heckeUpperSubgroup N ℓ) :
    (sourceIntegralHeckeConjugate g).val.val =
      !![g.val.val 0 0, g.val.val 0 1 / (ℓ : ℤ);
        g.val.val 1 0 * (ℓ : ℤ), g.val.val 1 1] := rfl

/-- The distinguished cusp orbit contributes exactly ell times the
original cusp value at the divided primitive column. -/
theorem termOf_u (δ : SL(2, ℤ)) (hδ : (ℓ : ℤ) ∣ δ 0 0)
    (φ : Additive (Gamma0 N) →+ A) :
    ∃ σ₂ : SL(2, ℤ), σ₂ 0 0 * ℓ = δ 0 0 ∧ σ₂ 1 0 = δ 1 0 ∧
      termOf hℓ φ (uOf N δ) (uOf_mem_upper δ hδ) = ℓ • B φ σ₂ := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hae := isCoprime_col δ
  obtain ⟨a', ha'⟩ := id hδ
  have ha'e : IsCoprime a' (δ 1 0) := by rw [ha'] at hae; exact hae.of_mul_left_right
  obtain ⟨σ₂, hσ00, hσ10⟩ := ha'e.exists_SL2_col (0 : Fin 2)
  refine ⟨σ₂, by rw [hσ00, ha', mul_comm], hσ10, ?_⟩
  let g : heckeUpperSubgroup N ℓ := ⟨uOf N δ, uOf_mem_upper δ hδ⟩
  have hg : g.val.val = unipMat (δ 0 0) (δ 1 0) N := coe_uOf_eq_unipMat δ
  have hkey : sourceHeckeConjugation hℓ g = uOf N σ₂ ^ ℓ := by
    rw [← sourceIntegralHeckeConjugate_eq_prime]
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_uOf_eq_unipMat, unipMat_pow]
    apply Subtype.ext
    rw [integralConjugate_entries, hg, hσ00, hσ10, ha']
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [unipMat]
    · ring
    · rw [show (N : ℤ) * (ℓ * a') * (ℓ * a') = ℓ * (N * a' * (ℓ * a')) by ring,
        Int.mul_ediv_cancel_left _ hℓ0]
      ring
    · ring
    · ring
  change φ (Additive.ofMul (sourceHeckeConjugation hℓ g)) = _
  rw [hkey, ofMul_pow, map_nsmul]
  rfl

/-- Every nonfixed original cusp orbit contributes the original cusp value
at the primitive column with its second coordinate multiplied by ell. -/
theorem termOf_other (δ : SL(2, ℤ)) (hδ : (ℓ : ℤ) ∣ δ 0 0)
    (φ : Additive (Gamma0 N) →+ A) (r : Gamma0 N) (hr : r ∉ heckeUpperSubgroup N ℓ)
    (hm : r⁻¹ * uOf N δ ^ ℓ * r ∈ heckeUpperSubgroup N ℓ) :
    ∃ σ₁ : SL(2, ℤ), σ₁ 0 0 = pOf δ r ∧ σ₁ 1 0 = ℓ * qOf δ r ∧
      termOf hℓ φ (r⁻¹ * uOf N δ ^ ℓ * r) hm = B φ σ₁ := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h => hr ((dvd_pOf_iff δ hℓ hδ r).mp h)
  have hpq : IsCoprime (pOf δ r) (qOf δ r) := isCoprime_col _
  have hpℓq : IsCoprime (pOf δ r) ((ℓ : ℤ) * qOf δ r) :=
    IsCoprime.mul_right ((Prime.coprime_iff_not_dvd hprime).mpr hp).symm hpq
  obtain ⟨σ₁, hσ00, hσ10⟩ := hpℓq.exists_SL2_col (0 : Fin 2)
  refine ⟨σ₁, hσ00, hσ10, ?_⟩
  let g : heckeUpperSubgroup N ℓ := ⟨r⁻¹ * uOf N δ ^ ℓ * r, hm⟩
  have hg : g.val.val = unipMat (pOf δ r) (qOf δ r) ((N : ℤ) * ℓ) :=
    coe_inv_mul_pow_mul δ r ℓ
  have hkey : sourceHeckeConjugation hℓ g = uOf N σ₁ := by
    rw [← sourceIntegralHeckeConjugate_eq_prime]
    apply Subtype.ext
    rw [coe_uOf_eq_unipMat]
    apply Subtype.ext
    rw [integralConjugate_entries, hg, hσ00, hσ10]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [unipMat]
    · ring
    · rw [show (N : ℤ) * ℓ * pOf δ r * pOf δ r = ℓ * (N * pOf δ r * pOf δ r) by ring,
        Int.mul_ediv_cancel_left _ hℓ0]
    · ring
    · ring
  change φ (Additive.ofMul (sourceHeckeConjugation hℓ g)) = _
  rw [hkey]
  rfl

end
end Dubon2026.SourceCuspBoundary
