import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! DUB-17/18 -> residual Galois association -> nonparabolic weight-two
branch -> reduction of the genuine complex Dirichlet characters through
the same map constructed for the original integral eigenvalues. Finite
order and the pinned integral-power theorem derive integrality; inverses
remain units under the prescribed reduction. Adapted from the archived
Apache-2.0 anthropics/fermats-last-theorem revision
6e837e75355538c7f80bab5b956861e86c4eacc2, weight-two residual association.
-/
namespace Dubon2026
noncomputable section

/-- Every actual finite-group complex unit character has integral values. -/
theorem sourceFiniteCharacter_isIntegral {G : Type*} [Group G] [Finite G] (e : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((e g : ℂˣ) : ℂ) := by
  have hg : IsOfFinOrder g := isOfFinOrder_of_finite g
  obtain ⟨m, hm, hgm⟩ := hg.exists_pow_eq_one
  apply IsIntegral.of_pow hm
  have he : ((e g : ℂˣ) : ℂ) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hgm, map_one, Units.val_one]
  rw [he]
  exact isIntegral_one

/-- Reduction of a genuine finite unit character through the original integral reduction map. -/
def sourceFiniteCharacterReduction {G : Type*} [Group G] [Finite G] {κ : Type*} [CommRing κ]
    (φ' : integralClosure ℤ ℂ →+* κ) (e : G →* ℂˣ) : G →* κˣ where
  toFun g :=
    ⟨φ' ⟨(e g : ℂ), sourceFiniteCharacter_isIntegral e g⟩, φ' ⟨(e g⁻¹ : ℂ), sourceFiniteCharacter_isIntegral e g⁻¹⟩,
      by
        rw [← map_mul, ← map_one φ']
        congr 1
        apply Subtype.ext
        change ((e g : ℂˣ) : ℂ) * ((e g⁻¹ : ℂˣ) : ℂ) = 1
        rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one],
      by
        rw [← map_mul, ← map_one φ']
        congr 1
        apply Subtype.ext
        change ((e g⁻¹ : ℂˣ) : ℂ) * ((e g : ℂˣ) : ℂ) = 1
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩
  map_one' := by
    apply Units.ext
    change φ' ⟨((e 1 : ℂˣ) : ℂ), _⟩ = 1
    rw [← map_one φ']
    congr 1
    apply Subtype.ext
    change ((e 1 : ℂˣ) : ℂ) = 1
    rw [map_one, Units.val_one]
  map_mul' g h := by
    apply Units.ext
    change φ' ⟨((e (g * h) : ℂˣ) : ℂ), _⟩ = φ' ⟨((e g : ℂˣ) : ℂ), _⟩ * φ' ⟨((e h : ℂˣ) : ℂ), _⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change ((e (g * h) : ℂˣ) : ℂ) = ((e g : ℂˣ) : ℂ) * ((e h : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul]

/-- The reduced character has exactly the original integral values under the prescribed reduction. -/
theorem sourceFiniteCharacterReduction_apply {G : Type*} [Group G] [Finite G] {κ : Type*} [CommRing κ]
    (φ' : integralClosure ℤ ℂ →+* κ) (e : G →* ℂˣ) (g : G) :
    ((sourceFiniteCharacterReduction φ' e g : κˣ) : κ) = φ' ⟨(e g : ℂ), sourceFiniteCharacter_isIntegral e g⟩ := rfl

end
end Dubon2026
