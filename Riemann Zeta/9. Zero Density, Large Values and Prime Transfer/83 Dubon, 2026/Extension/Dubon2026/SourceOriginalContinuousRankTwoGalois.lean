import Dubon2026.SourceOriginalRankTwoHeckeGalois
import Dubon2026.SourceOriginalRationalTateContinuity
import Dubon2026.SourceRankTwoCoordinateTopology

/-! DUB-17/18 -> original modular Galois association -> a continuous
rank-two Hecke Galois representation. The original finite Tate module
forces the constructed coefficient algebra to be finite. The canonical
p-adic module topology and native matrix units give a continuous GL2
representation with exactly the original rational Tate action. Eigenvalue
factors and Frobenius/inertia identities remain required. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => originalRationalTateModule N p

theorem originalRationalTate_finite : Module.Finite ℚ_[p] V := by
  letI : Module.Finite ℤ_[p] (TateModule p (originalJZero N)) :=
    (original_tate_free_finite_rank N p).2.1
  infer_instance

theorem originalRationalTateGalois_all_continuous_apply
    [TopologicalSpace V] [IsModuleTopology ℚ_[p] V] (x : V) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar => originalRationalTateGaloisRep N p σ x) := by
  letI : Module.Free ℤ_[p] (TateModule p (originalJZero N)) :=
    (original_tate_free_finite_rank N p).1
  letI : Module.Finite ℤ_[p] (TateModule p (originalJZero N)) :=
    (original_tate_free_finite_rank N p).2.1
  exact originalRationalTateGalois_continuous_apply N p
    (Module.finBasis ℤ_[p] (TateModule p (originalJZero N))) x

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalRationalTate_continuous_rankTwo_hecke_galois :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T) (_ : Module.Finite ℚ_[p] T)
      (χ : Nat.Primes → T) (e : V ≃ₗ[ℚ_[p]] (Fin 2 → T))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* Matrix.GeneralLinearGroup (Fin 2) T),
      Algebra.adjoin ℚ_[p] (Set.range χ) = ⊤ ∧
      (∀ (ell : Nat.Primes) (x : V),
        e ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange
          ℚ_[p] x) = χ ell • e x) ∧
      (letI : TopologicalSpace T := moduleTopology ℚ_[p] T
       Continuous ρ) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : V),
        (ρ σ).val *ᵥ e x = e (originalRationalTateGaloisRep N p σ x) := by
  obtain ⟨T, hT, hA, χ, e, τ, hgen, hact, he⟩ := originalRationalTate_rankTwo_hecke_galois N p
  letI : Module.Finite ℚ_[p] V := originalRationalTate_finite N p
  letI : Module.Finite ℚ_[p] T := finite_coefficients_of_rankTwo e
  letI : TopologicalSpace V := moduleTopology ℚ_[p] V
  letI : TopologicalSpace T := moduleTopology ℚ_[p] T
  letI : IsTopologicalRing T := IsModuleTopology.isTopologicalRing ℚ_[p] T
  refine ⟨T, hT, hA, inferInstance, χ, e, rankTwoGeneralLinearRep τ, hgen, hact, ?_, ?_⟩
  · exact rankTwoGeneralLinearRep_continuous τ
      (rankTwo_coordinate_action_continuous e (originalRationalTateGaloisRep N p) τ he
        (originalRationalTateGalois_all_continuous_apply N p))
  · intro σ x
    exact (rankTwoGeneralLinearRep_action τ σ (e x)).trans (he σ x)

end
end Dubon2026.SourceFunctionField.OriginalChart
