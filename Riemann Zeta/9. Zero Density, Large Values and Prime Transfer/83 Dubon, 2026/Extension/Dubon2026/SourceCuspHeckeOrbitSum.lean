import Dubon2026.SourceCuspHeckeTerms
import Dubon2026.SourceCosetTransfer

/-! DUB-17/18 -> residual Galois association -> boundary eigensystems
of the original complex class -> its complete Hecke cusp sum. The existing
original coset-transfer comparison and pinned orbit formula retain every
original correspondence term.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open CongruenceSubgroup

variable {N ℓ : ℕ} [NeZero ℓ]

private local instance upperIndex : (heckeUpperSubgroup N ℓ).FiniteIndex :=
  sourceHeckeUpper_finiteIndex

private local instance upperFinite : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :=
  sourceHeckeUpperFintype N ℓ

/-- The complete original Hecke coset sum is the exact sum of its actual
cusp-orbit contributions, with the original subgroup representatives. -/
theorem hecke_sum_eq_sum_orbits (hℓ : ℓ.Prime) {A : Type} [AddCommGroup A]
    (φ : Additive (Gamma0 N) →+ A) (u : Gamma0 N) :
    letI : Fintype (OrbQ N ℓ u) := Fintype.ofFinite _
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ,
      φ (Additive.ofMul (sourceHeckeConjugation hℓ
        (cosetTransition (heckeUpperSubgroup N ℓ) u q)))) =
      ∑ O : OrbQ N ℓ u,
        termOf hℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
          (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) := by
  classical
  letI : Fintype (OrbQ N ℓ u) := Fintype.ofFinite _
  let ψ : heckeUpperSubgroup N ℓ →* Multiplicative A :=
    (AddMonoidHom.toMultiplicativeRight φ).comp (sourceHeckeConjugation hℓ)
  have he := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ψ u
  rw [sourceTransfer_eq_coset_product] at he
  have ha := congrArg Multiplicative.toAdd he
  rw [toAdd_prod, toAdd_prod] at ha
  exact ha

end
end Dubon2026.SourceCuspBoundary
