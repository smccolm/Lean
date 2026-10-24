import Dubon2026.LocalResidueRootSeparation
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic

/-! DUB-17/18 -> characteristic-two faithful inertia -> Deuring cubic generators.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, faithful Deuring good-model field.
The local-domain root-separation theorem already proved in this repository
replaces the source's special cubic valuation argument. -/
namespace Dubon2026.SourceEllipticDeuring
open IsLocalRing
open scoped Pointwise
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] (A : ValuationSubring M)

lemma val_sub_lt_one_of_inertia {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) (a : A) :
    A.valuation (σ a - a) < 1 := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩ = 1 := hσI
  have hσa : σ a ∈ A := by
    have h := ValuationSubring.smul_mem_pointwise_smul σ (a : M) A a.2
    rwa [MulAction.mem_stabilizer_iff.mp hσ] at h
  have hres : residue A ⟨σ a, hσa⟩ = residue A a := by
    have : residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup F) • a) = residue A a := by
      rw [IsLocalRing.ResidueField.residue_smul]
      show MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩
        (residue A a) = residue A a
      rw [h1]; rfl
    exact this
  have hmem : (⟨σ a, hσa⟩ : A) - a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  exact (A.valuation_lt_one_iff _).mp hmem

lemma smul_mem_of_decomposition {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F) {a : M}
    (ha : a ∈ A) : σ a ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul σ a A ha
  rwa [MulAction.mem_stabilizer_iff.mp hσ] at h

lemma eq_one_of_cube_eq_one (h3 : IsUnit (3 : A)) {ζ : M} (hζA : A.valuation ζ ≤ 1) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : A.valuation (ζ - 1) < 1) : ζ = 1 := by
  let z : A := ⟨ζ, (A.valuation_le_one_iff ζ).mp hζA⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext hζ3
  have h3r : (3 : ResidueField A) ≠ 0 := by
    simpa only [map_ofNat] using (h3.map (residue A)).ne_zero
  have hr : residue A z = 1 := by
    have hm : z - 1 ∈ IsLocalRing.maximalIdeal A :=
      (A.valuation_lt_one_iff _).mpr hζ1
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hm
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz
  exact congrArg Subtype.val (local_eq_one_of_residue_eq_one_of_pow_eq_one hz3 h3r hr)

lemma eq_of_inertia_of_cube_eq (h3 : IsUnit (3 : A)) {σ : M ≃ₐ[F] M}
    (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) {x : M}
    (hx : A.valuation x = 1) (hcube : σ (x ^ 3) = x ^ 3) : σ x = x := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have hσxA : σ x ∈ A := smul_mem_of_decomposition A hσ hxA
  set ζ : M := σ x / x with hζ
  have hζx : σ x = ζ * x := by rw [hζ, div_mul_cancel₀ _ hx0]
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, div_pow, ← map_pow, hcube, div_self (pow_ne_zero 3 hx0)]
  have hζA : A.valuation ζ ≤ 1 := by
    rw [hζ, map_div₀, hx, div_one]; exact (A.valuation_le_one_iff _).mpr hσxA
  have hζ1 : A.valuation (ζ - 1) < 1 := by
    have h := val_sub_lt_one_of_inertia A hσ hσI ⟨x, hxA⟩
    simp only at h
    have : ζ - 1 = (σ x - x) / x := by rw [hζ]; field_simp
    rw [this, map_div₀, hx, div_one]; exact h
  rw [hζx, eq_one_of_cube_eq_one A h3 hζA hζ3 hζ1, one_mul]

lemma val_eq_one_of_pow {x : M} {n : ℕ} (hn : n ≠ 0) (h : A.valuation (x ^ n) = 1) :
    A.valuation x = 1 := by
  rw [Valuation.map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hn).mp h

end
end Dubon2026.SourceEllipticDeuring
