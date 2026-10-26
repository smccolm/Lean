import Dubon2026.SourceNormValuationRestriction
import Dubon2026.RationalPrimeOriginalNormPrime
import Dubon2026.EmbeddedNormalGaloisRestriction

/-! DUB-17/18 -> prescribed residual association -> actual rational local
interfaces. Every original global-to-local embedding gives its literal
pulled-back valuation. The selected rational prime is a nonunit and the
same normal restriction preserves the source Frobenius/inertia conditions. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
variable (p : ℕ) (hp : p.Prime)
local notation "K" => rationalPrimeLocalField p hp
local notation "L" => rationalPrimeLocalClosure p hp
theorem sourceRationalAlgebraicClosure_isGalois : IsGalois ℚ Qbar := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ Qbar) := Subsingleton.elim _ _
  letI : IsAlgClosure ℚ Qbar := by
    have h := AlgebraicClosure.instIsAlgClosure ℚ
    rw [hAlg] at h
    exact h
  exact ⟨⟩

private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- The actual original local norm valuation pulled back to the chosen global algebraic closure. -/
def sourceRationalLocalValuation (e : Qbar →ₐ[ℚ] L) : ValuationSubring Qbar :=
  (algebraicLocalIntegerRing L).comap e.toRingHom

theorem sourceRationalLocalValuation_prime (e : Qbar →ₐ[ℚ] L) :
    (p : Qbar) ∈ (sourceRationalLocalValuation p hp e).nonunits := by
  apply (valuation_comap_nonunits_iff (algebraicLocalIntegerRing L) e.toRingHom _).mpr
  rw [map_natCast]
  have hn := rationalPrimeOriginalClosureNorm_prime_lt_one p hp
  let x : algebraicLocalIntegerRing L := ⟨(p : L), by
    change ‖(p : L)‖₊ ≤ 1
    exact_mod_cast hn.le⟩
  change (x : L) ∈ (algebraicLocalIntegerRing L).nonunits
  apply ValuationSubring.coe_mem_nonunits_iff.mpr
  rw [Valuation.mem_maximalIdeal_iff]
  exact_mod_cast hn

theorem sourceRationalLocalValuation_frobenius (e : Qbar →ₐ[ℚ] L) (g : Gal(L/K))
    (hg : ∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), g • z = z ^ p) :
    ∃ hd : embeddedNormalGaloisRestriction e g ∈
        (sourceRationalLocalValuation p hp e).decompositionSubgroup ℚ,
      ∀ z : IsLocalRing.ResidueField (sourceRationalLocalValuation p hp e),
        (⟨embeddedNormalGaloisRestriction e g, hd⟩ :
          (sourceRationalLocalValuation p hp e).decompositionSubgroup ℚ) • z = z ^ p :=
  norm_restriction_frobenius e.toRingHom g (embeddedNormalGaloisRestriction e g)
    (embeddedNormalGaloisRestriction_commutes e g) p hg

theorem sourceRationalLocalValuation_inertia (e : Qbar →ₐ[ℚ] L) (g : Gal(L/K))
    (hg : g ∈ rationalPrimeNormInertia p hp) :
    embeddedNormalGaloisRestriction e g ∈
      ((sourceRationalLocalValuation p hp e).inertiaSubgroup ℚ).map
        ((sourceRationalLocalValuation p hp e).decompositionSubgroup ℚ).subtype :=
  norm_restriction_inertia e.toRingHom g (embeddedNormalGaloisRestriction e g)
    (embeddedNormalGaloisRestriction_commutes e g) hg

end
end Dubon2026
