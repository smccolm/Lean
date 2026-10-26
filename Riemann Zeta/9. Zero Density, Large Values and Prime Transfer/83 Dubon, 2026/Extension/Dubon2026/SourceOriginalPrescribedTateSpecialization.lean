import Dubon2026.SourceOriginalPrimitiveTateSpecialization

/-! DUB-17/18 -> all-weight residual association -> compatibility with
the prescribed coefficient reduction. The existing original p-adic Hecke
character accepts any prescribed Fourier-field embedding. Apply that
character to the already constructed continuous rank-two original Tate
action, keeping this exact embedding in every eigenvalue. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ
variable {E : Type*} [Field E] [Algebra ℚ_[ell] E]
variable [TopologicalSpace E] [IsModuleTopology ℚ_[ell] E]
private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩
open scoped IsMulCommutative

theorem originalPrimitiveTate_prescribed_specialization_of_basis {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    ∃ (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
        π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
          (fun i => τ (sourcePrimitiveFieldCoefficient f q.val) * π x i)) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
        (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x) := by
  let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) ell
  letI : IsMulCommutative T :=
    SourceHeckeMatrixDescent.Tp_commutative (originalLatticeHeckeMatrix N b lb) ell
  letI : CommRing T := inferInstance
  letI : TopologicalSpace T := moduleTopology ℚ_[ell] T
  letI := IsModuleTopology.toContinuousAdd ℚ_[ell] E
  let κ := originalPadicHeckeEigencharacter N ell b lb f τ
  have hκ : Continuous κ := IsModuleTopology.continuous_of_linearMap κ.toLinearMap
  have hsrc := originalRationalTate_explicit_continuous_galois N ell b P₀ lb
  rcases hsrc with ⟨e, ρ, hH, hρ, hact⟩
  let π := (rankTwoCoefficientMap κ).comp e.toLinearMap
  refine ⟨π, rankTwoCoefficientGaloisRep κ ρ,
    rankTwoCoefficientGaloisRep_continuous κ ρ hκ hρ, rankTwoCoefficientMap_span κ e, ?_, ?_⟩
  · intro q x
    exact (congrArg (rankTwoCoefficientMap κ) (hH q x)).trans
      ((rankTwoCoefficientMap_smul κ _ (e x)).trans
        (congrArg (fun c : E => fun i => c * π x i)
          (originalPadicHeckeEigencharacter_prime N ell b lb f τ q)))
  · intro σ x
    exact (rankTwoCoefficientGaloisRep_action κ ρ σ (e x)).trans
      (congrArg (rankTwoCoefficientMap κ) (hact σ x))

theorem originalPrimitive_prescribed_continuous_galois_realization
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    ∃ (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
        π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
          (fun i => τ (sourcePrimitiveFieldCoefficient f q.val) * π x i)) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
        (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x) := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ V
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  exact originalPrimitiveTate_prescribed_specialization_of_basis N ell b P₀
    (originalPeriodLatticeBasis N b) f τ

end
end Dubon2026.SourceFunctionField.OriginalChart
