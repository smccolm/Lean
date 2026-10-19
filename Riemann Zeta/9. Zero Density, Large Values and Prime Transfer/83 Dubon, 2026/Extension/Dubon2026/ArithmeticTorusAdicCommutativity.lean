import Dubon2026.ArithmeticTorusAdicPrimaryDescent
import Dubon2026.AdicMatrixProductEmbedding

/-! Regular auxiliary lifts have abelian local image over the actual
Noetherian adic coefficients. The proved whole-character decomposition in
each Artinian quotient and original adic separation give this directly.
This permits one Frobenius eigenbasis for the local-ring parameters needed
by the Dubon Theorem 2.6 arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

private theorem diagonalCharacterRepresentation_commute
    {A G ι : Type*} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι]
    (ρ : G →* GeneralLinearGroup ι A) (W : GeneralLinearGroup ι A)
    (χ : G →* (ι → A)ˣ)
    (hχ : ∀ g, diagonal (χ g).val = (MulAut.conj W (ρ g)).val)
    (g h : G) : Commute (ρ g) (ρ h) := by
  let D := Units.map (diagonalRingHom ι A).toMonoidHom
  have he (x) : D (χ x) = MulAut.conj W (ρ x) := Units.ext (hχ x)
  change ρ g * ρ h = ρ h * ρ g
  apply (MulAut.conj W).injective
  rw [map_mul, map_mul, ← he g, ← he h, ← D.map_mul, ← D.map_mul]
  exact congrArg D (mul_comm (χ g) (χ h))

private theorem adicTorus_powerReduction_commute
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes)
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g))
    (g h : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
    (n : ℕ) :
    Commute
      (GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
        (τ (rationalPrimeArithmeticRestriction b p.val p.property g)))
      (GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
        (τ (rationalPrimeArithmeticRestriction b p.val p.property h))) := by
  letI : Finite (ResidueField A) := Finite.of_injective eA eA.injective
  let J := maximalIdeal A ^ (n + 1)
  let B := A ⧸ J
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
    (Ideal.pow_le_self (Nat.succ_ne_zero n))
  letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Finite B := finite_quotient_iff.mpr ⟨n + 1, le_rfl⟩
  letI : DiscreteTopology B := by
    change DiscreteTopology (A ⧸ maximalIdeal A ^ (n + 1))
    rw [← hA]
    exact adicPowerQuotient_discrete (n + 1)
  let eB := (localQuotientResidueAlgEquiv (O := A) J).symm.toRingEquiv.trans eA
  let τB := (GeneralLinearGroup.map (n := Fin (degree + 1)) (Ideal.Quotient.mk J)).comp τ
  have hc : Continuous τB := by
    change Continuous ((GeneralLinearGroup.map (n := Fin (degree + 1)) (Ideal.Quotient.mk J)) ∘ τ)
    apply Continuous.comp ?_ hτ
    change Continuous (GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))
    rw [← hA]
    exact adicMatrixPowerReduction_continuous (n + 1)
  have he : (eB.toRingHom.comp (residue B)).comp (Ideal.Quotient.mk J) =
      eA.toRingHom.comp (residue A) := by
    ext x
    change eA ((localQuotientResidueAlgEquiv (O := A) J).symm
      (residue B (Ideal.Quotient.mk J x))) = eA (residue A x)
    rw [← localQuotientResidueAlgEquiv_residue (O := A) J x, AlgEquiv.symm_apply_apply]
  have hr : ∀ x, GeneralLinearGroup.map (eB.toRingHom.comp (residue B))
      (τB (rationalPrimeArithmeticRestriction b p.val p.property x)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property x) := by
    intro x
    change ((GeneralLinearGroup.map (eB.toRingHom.comp (residue B))).comp
      (GeneralLinearGroup.map (Ideal.Quotient.mk J)))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property x)) = _
    rw [← GeneralLinearGroup.map_comp, he]
    exact hred x
  obtain ⟨_, _, _, W, χ, _, _, _, _, hχ, _, _, _⟩ :=
    rationalArithmetic_torus_global_lift_characters a b q degree level hlevel R p hgood eB τB hc hr
  exact diagonalCharacterRepresentation_commute
    (τB.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom) W χ hχ g h

/-- All local images of an actual selected-prime adic lift commute.
No compatible family of diagonal bases is required. -/
theorem rationalArithmetic_torus_global_adic_commute
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes)
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g))
    (g h : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property)) :
    Commute (τ (rationalPrimeArithmeticRestriction b p.val p.property g))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property h)) := by
  letI : IsHausdorff (WithIdeal.i : Ideal A) A := hA.symm ▸ inferInstance
  letI : T2Space A := (IsAdic.isHausdorff_iff (I := (WithIdeal.i : Ideal A)) rfl).mp inferInstance
  apply adicMatrixReductionProduct_injective (R := A) (ι := Fin (degree + 1))
  funext n
  change GeneralLinearGroup.map (Ideal.Quotient.mk ((WithIdeal.i : Ideal A) ^ n))
    (_ * _) = GeneralLinearGroup.map (Ideal.Quotient.mk ((WithIdeal.i : Ideal A) ^ n)) (_ * _)
  rw [hA, map_mul, map_mul]
  cases n with
  | zero =>
    letI : Subsingleton (A ⧸ maximalIdeal A ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    exact adicTorus_powerReduction_commute a b q degree level hlevel R p hgood
      hA eA τ hτ hred g h n

end
end Dubon2026
