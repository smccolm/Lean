import Dubon2026.SourceOriginalFullLatticeHeckeAlgebra

/-! DUB-17/18 -> rational rank-two Hecke realization -> compatibility
for every integral word in actual prime correspondences. Conjugation by
the proved arithmetic Tate tensor equivalence and the native scalar
extension algebra homomorphism agree on each generator. Freeness extends
this equality to every word, so all integral operator relations are kept.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
open scoped TensorProduct
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

/-- Integral prime words act by the literal arithmetic Picard correspondences on Tate sequences. -/
def originalTateHeckeWord (p : ℕ) [Fact p.Prime] :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End ℤ_[p] (TateModule p (originalJZero N)) :=
  FreeAlgebra.lift ℤ (fun ell : Nat.Primes =>
    TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val))

theorem originalTateHeckeWord_generator (p : ℕ) [Fact p.Prime] (ell : Nat.Primes) :
    originalTateHeckeWord N p (FreeAlgebra.ι ℤ ell) =
      TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val) :=
  FreeAlgebra.lift_ι_apply _ ell

theorem originalTateHeckeWord_conjugate (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ((originalTatePeriodTensorEquiv N p b P₀ lb).conjAlgEquiv ℤ).toAlgHom.comp
        (originalTateHeckeWord N p) =
      (Module.End.baseChangeHom ℤ ℤ_[p] (pathPeriodLattice N (fun i => (b i).val))).comp
        (originalLatticeHeckeWord N b) := by
  apply FreeAlgebra.hom_ext
  funext ell
  apply LinearMap.ext
  intro y
  simp only [Function.comp_apply, AlgHom.comp_apply, originalTateHeckeWord_generator,
    originalLatticeHeckeWord_generator]
  let e := originalTatePeriodTensorEquiv N p b P₀ lb
  change e (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)
      (e.symm y)) = (originalPrimePeriodLatticeHecke N ell b).baseChange ℤ_[p] y
  exact (originalTatePeriodTensorEquiv_originalPrimeHecke N ell p b P₀ lb (e.symm y)).trans
    (congrArg ((originalPrimePeriodLatticeHecke N ell b).baseChange ℤ_[p])
      (e.apply_symm_apply y))

theorem originalTatePeriodTensorEquiv_heckeWord (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) (x : TateModule p (originalJZero N)) :
    originalTatePeriodTensorEquiv N p b P₀ lb (originalTateHeckeWord N p a x) =
      (originalLatticeHeckeWord N b a).baseChange ℤ_[p]
        (originalTatePeriodTensorEquiv N p b P₀ lb x) := by
  let e := originalTatePeriodTensorEquiv N p b P₀ lb
  have he := DFunLike.congr_fun (originalTateHeckeWord_conjugate N p b P₀ lb) a
  have hx := LinearMap.congr_fun he (e x)
  change e (originalTateHeckeWord N p a (e.symm (e x))) =
    (originalLatticeHeckeWord N b a).baseChange ℤ_[p] (e x) at hx
  exact (congrArg (fun y : TateModule p (originalJZero N) => e (originalTateHeckeWord N p a y))
    (e.symm_apply_apply x)).symm.trans hx

end
end Dubon2026.SourceFunctionField.OriginalChart
