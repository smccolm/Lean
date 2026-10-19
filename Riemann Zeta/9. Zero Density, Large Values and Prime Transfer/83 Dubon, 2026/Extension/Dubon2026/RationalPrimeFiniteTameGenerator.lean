import Dubon2026.AlgebraicLocalFiniteTameGenerator
import Dubon2026.RationalPrimeNormResidueCard
import Dubon2026.RationalPrimeOriginalNormPrime
import Dubon2026.TameFrobeniusOrder
import Dubon2026.NormLocalResidueFinite

/-! The same original rational-prime local field supplies arithmetic
Frobenius, a finite tame generator and normal wild subgroup. Their exponent is
the original rational prime; tame order is coprime to it. This discharges the
finite local Galois presentation input of DUB-17's ramified auxiliary condition. -/

namespace Dubon2026
noncomputable section

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem rationalPrimeOriginalNorm_exists_frobenius (p : ℕ) (hp : p.Prime) :
    ∃ φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
      ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp)),
        φ • x = x ^ p := by
  let K := rationalPrimeLocalField p hp
  let L := rationalPrimeLocalClosure p hp
  letI : Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) := normLocal_residue_finite K
  obtain ⟨φ, hφ⟩ := algebraicLocal_exists_residueFrobenius K L
  refine ⟨φ, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rw [← IsLocalRing.ResidueField.residue_smul, hφ, rationalPrimeOriginalNorm_residue_card p hp]

theorem rationalPrime_exists_finite_tame_generator
    (p : ℕ) (hp : p.Prime) {F : Type} [Field F] [NumberField F]
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x)) :
    let I := (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)
    ∃ (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
      (t : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker)
      (W : Subgroup (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker))
      (hW : W.Normal),
      letI := hW
      t ∈ I ∧ IsPGroup p W ∧ W ≤ I ∧ I = W ⊔ Subgroup.zpowers t ∧
      (QuotientGroup.mk' r.ker φ) * t * (QuotientGroup.mk' r.ker φ)⁻¹ * (t ^ p)⁻¹ ∈ W ∧
      Nat.Coprime p (orderOf (QuotientGroup.mk' W t)) := by
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius p hp
  obtain ⟨t, W, ht, hW, hWp, hWle, hgen, hrel⟩ :=
    algebraicLocal_exists_finite_tame_generator e p hp
      (rationalPrimeOriginalClosureNorm_prime_lt_one p hp) r he φ hφ
  letI := hW
  letI : Finite (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) :=
    Finite.of_injective (QuotientGroup.kerLift r) (QuotientGroup.kerLift_injective r)
  refine ⟨φ, t, W, hW, ht, hWp, hWle, hgen, hrel, ?_⟩
  apply finite_frobenius_relation_order_coprime p hp
    (QuotientGroup.mk' W (QuotientGroup.mk' r.ker φ)) (QuotientGroup.mk' W t)
  have h := (QuotientGroup.eq_one_iff _).mpr hrel
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
    mul_inv_eq_one] using h

end
end Dubon2026
