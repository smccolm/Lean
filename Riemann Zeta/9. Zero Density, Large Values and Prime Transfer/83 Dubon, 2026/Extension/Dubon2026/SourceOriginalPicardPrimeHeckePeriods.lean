import Dubon2026.SourceOriginalPrimeHeckeAbelQuotient
import Dubon2026.SourceOriginalPicardAbelMap

/-! DUB-17/18 -> original Jacobian Tate Hecke realization -> full
original Picard-period compatibility. The proved moving theorem reduces
every degree-zero divisor to analytic point differences plus an actual
principal divisor. Both original operators kill the latter by the proved
principal-divisor theorem and genuine Hecke norm correspondence.
The result applies to every original Picard class, not just analytic
generators. No moving, Abel, lattice or compatibility premise remains, including at primes dividing the level.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

private local instance (ell : Nat.Primes) : NeZero ell.val :=
  ⟨ell.property.ne_zero⟩

theorem originalPrimePeriodQuotientHecke_abel_divisor
    (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD : Divisor.degree D = 0) :
    originalPrimePeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ
          (abelJacobiDiv N (fun i => (b i).val) P₀ D)) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (abelJacobiDiv N (fun i => (b i).val) P₀ (originalHeckeDivisor ℂ N ell.val D)) := by
  obtain ⟨E, c, hE, _, hc, rfl⟩ := exists_original_degree_zero_analytic_representative N D hD
  have hE0 : (pathPeriodLattice N (fun i => (b i).val)).mkQ
      (abelJacobiDiv N (fun i => (b i).val) P₀ E) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      (original_abelJacobiDiv_mem_of_isPrincipal N b P₀ E hE)
  have hHE0 : (pathPeriodLattice N (fun i => (b i).val)).mkQ
      (abelJacobiDiv N (fun i => (b i).val) P₀ (originalHeckeDivisor ℂ N ell.val E)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      (original_abelJacobiDiv_mem_of_isPrincipal N b P₀ _
        (isPrincipal_originalHeckeDivisor ℂ N ell.val hE))
  simp only [map_add, hE0, hHE0, zero_add]
  exact originalPrimePeriodQuotientHecke_analytic_divisor N ell b P₀ c hc

theorem originalAbelPic0_originalPrimeHecke (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (q : Pic0 ℂ F) :
    originalAbelPic0 N b P₀ (originalHeckePicard ℂ N ell.val q) =
      originalPrimePeriodQuotientHecke N ell b (originalAbelPic0 N b P₀ q) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective q
  rw [originalHeckePicard_mk, originalAbelPic0_mk, originalAbelPic0_mk]
  exact (originalPrimePeriodQuotientHecke_abel_divisor N ell b P₀ D.val D.property).symm

theorem originalPicardPeriodEquiv_originalPrimeHecke (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (q : Pic0 ℂ F) :
    originalPicardPeriodEquiv N b P₀ (originalHeckePicard ℂ N ell.val q) =
      originalPrimePeriodQuotientHecke N ell b (originalPicardPeriodEquiv N b P₀ q) :=
  originalAbelPic0_originalPrimeHecke N ell b P₀ q

end
end Dubon2026.SourceFunctionField.OriginalChart
