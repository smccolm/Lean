import Dubon2026.FiniteCongruenceImageSubgroup
import Dubon2026.NumberFieldPrimeOrderMatrix

/-! # Triviality of the actual finite arithmetic congruence stabilizer

The two faithful realizations are of the same original finite group:
its matrices over the number field and its conjugated local matrices.
Local reduction proves residue-primary order; rational cyclotomic rank
excludes that order. This discharges the torsion-free certificate needed
for DUB-17's actual unitary arithmetic stabilizers at a large prime.
-/

namespace Dubon2026

noncomputable section

open Matrix IsLocalRing

/-- The original finite arithmetic group is trivial at a sufficiently large congruence prime. -/
theorem finiteArithmeticCongruence_trivial
    {K R L ι A : Type*} [Field K] [NumberField K]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing L]
    [Fintype ι] [DecidableEq ι] [Group A] [Finite A]
    (p : ℕ) (hp : p.Prime) [CharP (ResidueField R) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (φ : R →+* L) (hφ : Function.Injective φ)
    (ρ : A →* GeneralLinearGroup ι K) (hρ : Function.Injective ρ)
    (τ : A →* GeneralLinearGroup ι L) (hτ : Function.Injective τ)
    (hlevel : τ.range ≤ (MatrixCongruenceKernel (ι := ι) (maximalIdeal R)).map
      (GeneralLinearGroup.map φ)) : ∀ a : A, a = 1 := by
  letI : Finite τ.range := Finite.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  have hP := finiteCongruenceImageSubgroup_isPGroup p hp φ hφ τ.range hlevel
  have hA : IsPGroup p A := hP.of_injective τ.rangeRestrict
    (fun x y h => hτ (congrArg Subtype.val h))
  intro a
  obtain ⟨k, hk⟩ := hA a
  have hM : (ρ a).val ^ (p ^ k) = 1 := by
    have h := congrArg (fun x : A => (ρ x).val) hk
    simpa only [map_pow, Units.val_pow_eq_pow_val, map_one, Units.val_one] using h
  have he := numberFieldMatrix_primary_order_eq_one K ι p hp hlarge (ρ a).val k hM
  apply hρ
  rw [map_one]
  exact Units.ext he

end
end Dubon2026
