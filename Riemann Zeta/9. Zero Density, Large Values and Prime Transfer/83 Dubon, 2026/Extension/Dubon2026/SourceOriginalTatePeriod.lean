import Dubon2026.SourceOriginalTateComparison
import Dubon2026.SourceTateTorusNaturality
import Dubon2026.SourceTateEquivalences

/-! DUB-17/18 -> original Jacobian Tate realization -> actual period lattice.
Compose the proved arithmetic-to-complex comparison with the actual Abel
equivalence. The explicit p-adic lattice comparison then realizes the original
arithmetic Tate module as the scalar extension of this same integral lattice.
The formula on lattice tensors retains the map needed for Hecke compatibility.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential OriginalConstantField
open scoped TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "F" => modularFunctionFieldOver N ℂ
variable {n : ℕ}

/-- The original arithmetic Tate module mapped into the actual period quotient. -/
def originalTatePeriodQuotientEquiv
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F) :
    TateModule p (originalJZero N) ≃ₗ[ℤ_[p]]
      TateModule p ((Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) := by
  let e := @originalPicardPeriodEquiv N _ n b P₀
  exact (originalTateComplexEquiv N p).trans (TateModule.ofAddEquiv p e)

theorem originalTatePeriodQuotientEquiv_apply
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (x : TateModule p (originalJZero N)) (k : ℕ) :
    ((originalTatePeriodQuotientEquiv N p b P₀ x : TateModule p
        ((Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])))) :
        ℕ → (Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) k =
      (@originalPicardPeriodEquiv N _ n b P₀)
        (complexPicardMap N ((x : ℕ → originalJZero N) k)) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original arithmetic Tate module as the p-adic extension of its period lattice. -/
def originalTatePeriodTensorEquiv
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])))) :
    TateModule p (originalJZero N) ≃ₗ[ℤ_[p]]
      ℤ_[p] ⊗[ℤ] pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) :=
  (originalTatePeriodQuotientEquiv N p b P₀).trans
    (TateModule.Period.phi2 ℂ p _ lb).symm

theorem originalTatePeriodTensorEquiv_symm_tmul
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))))
    (a : ℤ_[p]) (l : pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) :
    originalTatePeriodQuotientEquiv N p b P₀
        ((originalTatePeriodTensorEquiv N p b P₀ lb).symm (a ⊗ₜ l)) =
      a • TateModule.Period.iota ℂ p _ l := by
  simp only [originalTatePeriodTensorEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    TateModule.Period.phi2_tmul]

end
end Dubon2026.SourceFunctionField.OriginalChart
