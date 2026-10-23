import Dubon2026.SourceOriginalTateHeckePeriods

/-! DUB-17/18 -> rank-two Hecke/Frobenius realization -> actual integral
period realization of the original arithmetic Tate Hecke action. Restrict
the genuine dual analytic Hecke map to its proved invariant path lattice,
then instantiate the existing tensor naturality theorem. The resulting
identity relates the literal arithmetic Picard correspondence to scalar
extension of this same integral operator; no lattice or naturality premise
is supplied by the caller.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
open scoped TensorProduct
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

private local instance {N : ℕ} (ell : sourceBinaryHeckePrime N) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The genuine dual analytic Hecke operator restricted to the actual integral path lattice. -/
def originalPeriodLatticeHecke (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    Module.End ℤ (pathPeriodLattice N (fun i => (b i).val)) :=
  ((originalPeriodHecke N ell b).restrictScalars ℤ).restrict
    (fun _ hv => originalPeriodHecke_preserves_path_lattice N ell b hv)

theorem originalPeriodLatticeHecke_coe (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (l : pathPeriodLattice N (fun i => (b i).val)) :
    (originalPeriodLatticeHecke N ell b l).val = originalPeriodHecke N ell b l.val := rfl

theorem originalPeriodQuotientHecke_eq_quotEnd (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    (originalPeriodQuotientHecke N ell b).toAddMonoidHom =
      TateModule.Period.quotEnd ℂ (pathPeriodLattice N (fun i => (b i).val))
        (originalPeriodHecke N ell b)
        (fun _ hv => originalPeriodHecke_preserves_path_lattice N ell b hv) := by
  ext q
  obtain ⟨v, rfl⟩ := (pathPeriodLattice N (fun i => (b i).val)).mkQ_surjective q
  rfl

theorem originalPeriod_phi2_latticeHecke
    (ell : sourceBinaryHeckePrime N) (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (z : ℤ_[p] ⊗[ℤ] pathPeriodLattice N (fun i => (b i).val)) :
    TateModule.Period.phi2 ℂ p _ lb ((originalPeriodLatticeHecke N ell b).baseChange ℤ_[p] z) =
      TateModule.tateMap p (originalPeriodQuotientHecke N ell b).toAddMonoidHom
        (TateModule.Period.phi2 ℂ p _ lb z) := by
  exact TateModule.Period.phi2_baseChange ℂ p _ lb (originalPeriodHecke N ell b)
    (fun _ hv => originalPeriodHecke_preserves_path_lattice N ell b hv)
    (originalPeriodLatticeHecke N ell b) (originalPeriodLatticeHecke_coe N ell b) z

theorem originalTatePeriodTensorEquiv_originalHecke
    (ell : sourceBinaryHeckePrime N) (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (x : TateModule p (originalJZero N)) :
    originalTatePeriodTensorEquiv N p b P₀ lb
        (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val) x) =
      (originalPeriodLatticeHecke N ell b).baseChange ℤ_[p]
        (originalTatePeriodTensorEquiv N p b P₀ lb x) := by
  let L := pathPeriodLattice N (fun i => (b i).val)
  have he : ∀ y, TateModule.Period.phi2 ℂ p L lb
      (originalTatePeriodTensorEquiv N p b P₀ lb y) =
        originalTatePeriodQuotientEquiv N p b P₀ y := by
    intro y
    exact (TateModule.Period.phi2 ℂ p L lb).apply_symm_apply
      (originalTatePeriodQuotientEquiv N p b P₀ y)
  apply (TateModule.Period.phi2 ℂ p L lb).injective
  exact (he _).trans ((originalTatePeriodQuotientEquiv_originalHecke N ell p b P₀ x).trans
    ((congrArg (TateModule.tateMap p (originalPeriodQuotientHecke N ell b).toAddMonoidHom)
      (he x).symm).trans
        (originalPeriod_phi2_latticeHecke N ell p b lb
          (originalTatePeriodTensorEquiv N p b P₀ lb x)).symm))

end
end Dubon2026.SourceFunctionField.OriginalChart
