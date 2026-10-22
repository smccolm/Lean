import Dubon2026.SourceOriginalAbelConverse
import Dubon2026.SourceOriginalJacobiInversion

/-! DUB-17/18 -> original torsion cardinality -> complex Picard comparison.
The actual Abel-divisor map descends through the actual principal-divisor
quotient. Its kernel is zero by the proved original Abel converse and its
image is the full period quotient by the existing original Jacobi inversion.
Adapted from S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

/-- The actual Abel map on degree-zero divisors, valued in the actual period quotient. -/
def originalAbelDegZero {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor.degZero (K := ℂ) («F» := F) →+ (Fin n → ℂ) ⧸ pathPeriodLattice N b :=
  (((pathPeriodLattice N b).mkQ.toAddMonoidHom).comp (abelJacobiDiv N b P₀)).comp
    (Divisor.degZero (K := ℂ) («F» := F)).subtype

theorem originalAbelDegZero_eq_zero_iff {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) («F» := F)) :
    originalAbelDegZero N b P₀ D = 0 ↔ abelJacobiDiv N b P₀ D.val ∈ pathPeriodLattice N b := by
  change (pathPeriodLattice N b).mkQ (abelJacobiDiv N b P₀ D.val) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The descended original Abel map on literal degree-zero divisor classes. -/
def originalAbelPic0 {n : ℕ} (b : Fin n → regularDifferentials ℂ F) (P₀ : Place ℂ F) :
    Pic0 ℂ F →+ (Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) :=
  QuotientAddGroup.lift _ (originalAbelDegZero N (fun i => (b i : Ω[F⁄ℂ])) P₀) fun D hD =>
    (originalAbelDegZero_eq_zero_iff N _ P₀ D).mpr
      (original_abelJacobiDiv_mem_of_isPrincipal N b P₀ D.val hD)

theorem originalAbelPic0_mk {n : ℕ} (b : Fin n → regularDifferentials ℂ F) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) («F» := F)) :
    originalAbelPic0 N b P₀ (Pic0.mk D) = originalAbelDegZero N (fun i => (b i : Ω[F⁄ℂ])) P₀ D := rfl

theorem originalAbelPic0_injective {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F) :
    Function.Injective (originalAbelPic0 N (fun i => b i) P₀) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective q
  rw [originalAbelPic0_mk, originalAbelDegZero_eq_zero_iff] at hq
  apply (Pic0.mk_eq_zero_iff D).mpr
  exact original_isPrincipal_of_abelJacobi_mem N b P₀ D.val D.property hq

theorem originalAbelPic0_surjective {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F) :
    Function.Surjective (originalAbelPic0 N (fun i => b i) P₀) := by
  intro q
  obtain ⟨u, rfl⟩ := (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))).mkQ_surjective q
  obtain ⟨D, hD0, hDu⟩ := original_jacobi_inversion N b P₀ u
  refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
  rw [originalAbelPic0_mk]
  change (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))).mkQ
    (abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D) = _
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).mpr hDu

/-- The original complex Picard group identified with its actual analytic period quotient. -/
def originalPicardPeriodEquiv {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F) :
    Pic0 ℂ F ≃+ (Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) :=
  AddEquiv.ofBijective (originalAbelPic0 N (fun i => b i) P₀)
    ⟨originalAbelPic0_injective N b P₀, originalAbelPic0_surjective N b P₀⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
