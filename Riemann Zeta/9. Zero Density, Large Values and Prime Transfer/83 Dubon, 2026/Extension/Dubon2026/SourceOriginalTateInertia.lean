import Dubon2026.SourceOriginalInertiaPicard
import Dubon2026.SourceOriginalRationalTateGalois

/-! DUB-17/18 -> original residual association -> unramified original
Tate action. Every genuine Tate coordinate is prime-power Picard torsion,
so the proved original Picard inertia theorem applies coordinatewise.
Native scalar extension preserves the identity on rational Tate space.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn.
Existing original Tate functor and reduction proofs replace external
representation and geometric certificates. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A

theorem originalTateGaloisRep_eq_one_of_inertia
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : kk) ≠ 0)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    originalTateGaloisRep N ell τ = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  rw [originalTateGaloisRep_apply]
  apply originalArithmeticPicard_eq_self_of_inertia_of_torsion A N p hp hNk
    (ell ^ n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hell) τ hτ
  exact (originalTateTorsionCoordinate N ell n x).property

theorem originalRationalTateGaloisRep_eq_one_of_inertia
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : kk) ≠ 0)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    OriginalChart.originalRationalTateGaloisRep N ell τ = 1 := by
  rw [OriginalChart.originalRationalTateGaloisRep_apply,
    originalTateGaloisRep_eq_one_of_inertia A N p hp hNk ell hell τ hτ]
  exact (Module.End.baseChangeHom ℤ_[ell] ℚ_[ell] (TateModule ell (originalJZero N))).map_one

theorem residue_charP_of_prime_mem_nonunits (p : ℕ) (hp : p.Prime)
    (hA : (p : Qbar) ∈ A.nonunits) : CharP kk p := by
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  have hm : (p : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hA
  have hr := (IsLocalRing.residue_eq_zero_iff (p : A)).mpr hm
  simpa only [map_natCast] using hr

theorem originalTateGaloisRep_eq_one_away_level_prime
    (ell : ℕ) [Fact ell.Prime] (p : ℕ) (hp : p.Prime) (hNp : ¬p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    originalTateGaloisRep N ell τ = 1 ∧
      OriginalChart.originalRationalTateGaloisRep N ell τ = 1 := by
  letI := residue_charP_of_prime_mem_nonunits A p hp hA
  have hN : (N : kk) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ p]
    exact fun h => hNp (dvd_mul_of_dvd_left h ell)
  have hell : (ell : kk) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ p]
    exact fun h => hNp (dvd_mul_of_dvd_right h N)
  exact ⟨originalTateGaloisRep_eq_one_of_inertia A N p hp hN ell hell τ hτ,
    originalRationalTateGaloisRep_eq_one_of_inertia A N p hp hN ell hell τ hτ⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
