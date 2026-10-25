import Dubon2026.SourceOriginalLatticeCuspHeckeEquiv
import Dubon2026.SourceOriginalRationalTatePrimeRankTwo
import Dubon2026.SourceHeckeCoordinateRelations

/-! DUB-17/18 -> primitive determinant -> the arithmetic primitive projector
on the original Tate module. The proved cusp/lattice word relations and
the actual rational Tate matrices factor the original action through the
same integral cusp Hecke algebra used to construct that projector. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalRationalTateHeckeWord_of_cusp_relation {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a c : FreeAlgebra ℤ Nat.Primes)
    (h : sourceIntegralCuspHeckeWord N a = sourceIntegralCuspHeckeWord N c) :
    originalRationalTateHeckeWord N p a = originalRationalTateHeckeWord N p c := by
  exact hecke_relation_of_injective_coordinates
    (originalFullLatticeHeckeWord N b) (originalRationalTateHeckeWord N p)
    (originalRationalTateBasis N p b P₀ lb).equivFun
    (originalRationalTateBasis N p b P₀ lb).equivFun.injective
    (fun t v => (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℚ_[p]) *ᵥ v)
    (originalRationalTateBasis_word_coordinates N p b P₀ lb)
    a c ((originalLatticeCuspHecke_same_relations N b a c).mpr h)

/-- The actual rational Tate action of the original integral cusp Hecke algebra. -/
def originalCuspRationalTateHecke {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    sourceOriginalIntegralHeckeAlgebra N 2 →+*
    Module.End ℚ_[p] (originalRationalTateModule N p) :=
  (sourceIntegralCuspHeckeWord N).toRingHom.liftOfSurjective
    (sourceIntegralCuspHeckeWord_surjective N)
    ⟨(originalRationalTateHeckeWord N p).toRingHom, by
      intro a ha
      have h : sourceIntegralCuspHeckeWord N a = sourceIntegralCuspHeckeWord N 0 :=
        (RingHom.mem_ker.mp ha).trans (map_zero _).symm
      exact RingHom.mem_ker.mpr
        ((originalRationalTateHeckeWord_of_cusp_relation N p b P₀ lb a 0 h).trans
          (map_zero _))⟩

theorem originalCuspRationalTateHecke_word {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalCuspRationalTateHecke N p b P₀ lb (sourceIntegralCuspHeckeWord N a) =
      originalRationalTateHeckeWord N p a :=
  RingHom.liftOfSurjective_comp_apply _ _ _ a

theorem originalCuspRationalTateHecke_prime {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (ell : Nat.Primes) :
    originalCuspRationalTateHecke N p b P₀ lb
      (sourceIntegralCuspHeckeWord N (FreeAlgebra.ι ℤ ell)) =
      (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
        ℚ_[p] := by
  rw [originalCuspRationalTateHecke_word]
  exact originalRationalTateHeckeWord_prime N p ell

end
end Dubon2026.SourceFunctionField.OriginalChart
