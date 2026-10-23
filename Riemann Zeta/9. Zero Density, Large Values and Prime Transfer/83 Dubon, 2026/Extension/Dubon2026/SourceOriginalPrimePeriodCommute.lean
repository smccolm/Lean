import Dubon2026.SourceOriginalPrimePeriodLattice
import Dubon2026.HeckeCommutativity

/-! DUB-17/18 -> rank-two original Hecke algebra realization -> the
commuting full prime operator family. Transport the already proved
analytic Hecke commutativity through the actual regular-cusp equivalence
and its basis-dual coordinates. The quotient uses the proved invariant
path lattice. No commutativity or comparison premise is assumed.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimeRegularHecke_commute (ell q : Nat.Primes) :
    Commute (originalPrimeRegularHecke N ell) (originalPrimeRegularHecke N q) := by
  apply LinearMap.ext
  intro w
  apply (originalRegularCuspEquiv N).injective
  change originalRegularCuspEquiv N (originalPrimeRegularHecke N ell
      (originalPrimeRegularHecke N q w)) =
    originalRegularCuspEquiv N (originalPrimeRegularHecke N q
      (originalPrimeRegularHecke N ell w))
  simp only [originalPrimeRegularHecke_cusp]
  have h := cuspHeckeLinear_prime_commute N 2 ell.property q.property
  rw [cuspHeckeLinear_prime N 2 ell.property, cuspHeckeLinear_prime N 2 q.property] at h
  exact congrArg (fun T : Module.End ℂ _ => T (originalRegularCuspEquiv N w)) h.eq

theorem originalPrimePeriodHecke_constr (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (v : Fin n → ℂ) :
    b.constr ℂ (originalPrimePeriodHecke N ell b v) =
      (b.constr ℂ v).comp (originalPrimeRegularHecke N ell) := by
  apply b.ext
  intro i
  simp only [Module.Basis.constr_basis, LinearMap.comp_apply]
  rfl

theorem originalPrimePeriodHecke_commute (ell q : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) :
    Commute (originalPrimePeriodHecke N ell b) (originalPrimePeriodHecke N q b) := by
  apply LinearMap.ext
  intro v
  funext i
  change b.constr ℂ (originalPrimePeriodHecke N q b v) (originalPrimeRegularHecke N ell (b i)) =
    b.constr ℂ (originalPrimePeriodHecke N ell b v) (originalPrimeRegularHecke N q (b i))
  rw [originalPrimePeriodHecke_constr, originalPrimePeriodHecke_constr]
  simp only [LinearMap.comp_apply]
  exact congrArg (b.constr ℂ v) (congrArg (fun T : Module.End ℂ V => T (b i))
    (originalPrimeRegularHecke_commute N q ell).eq)

theorem originalPrimePeriodQuotientHecke_commute (ell q : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) :
    Commute (originalPrimePeriodQuotientHecke N ell b)
      (originalPrimePeriodQuotientHecke N q b) := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (pathPeriodLattice N (fun i => (b i).val)).mkQ_surjective x
  change originalPrimePeriodQuotientHecke N ell b
      (originalPrimePeriodQuotientHecke N q b ((pathPeriodLattice N _).mkQ v)) =
    originalPrimePeriodQuotientHecke N q b
      (originalPrimePeriodQuotientHecke N ell b ((pathPeriodLattice N _).mkQ v))
  simp only [originalPrimePeriodQuotientHecke_mk]
  exact congrArg (pathPeriodLattice N (fun i => (b i).val)).mkQ
    (congrArg (fun T : Module.End ℂ (Fin n → ℂ) => T v)
      (originalPrimePeriodHecke_commute N ell q b).eq)

end
end Dubon2026.SourceFunctionField.OriginalChart
