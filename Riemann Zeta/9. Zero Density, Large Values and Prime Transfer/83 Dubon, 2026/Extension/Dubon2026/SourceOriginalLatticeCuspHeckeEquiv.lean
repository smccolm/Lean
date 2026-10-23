import Dubon2026.SourceOriginalCuspLatticeHeckeRelations
import Dubon2026.SourceSurjectiveHeckeWordEquiv
import Dubon2026.SourceIntegralCuspHeckeWords

/-! DUB-17/18 -> prescribed eigenform specialization -> identify the
actual original lattice Hecke algebra with the actual integral cusp Hecke
algebra. The proved identical relations and genuine surjective word maps
supply the equivalence, preserving each original prime generator. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

theorem originalLatticeCuspHecke_same_relations {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (a c : FreeAlgebra ℤ Nat.Primes) :
    originalFullLatticeHeckeWord N b a = originalFullLatticeHeckeWord N b c ↔
      sourceIntegralCuspHeckeWord N a = sourceIntegralCuspHeckeWord N c := by
  have h := originalLatticeHeckeWord_eq_iff_cusp N b (originalPeriodLatticeBasis N b) a c
  constructor
  · intro ha
    exact Subtype.ext (h.mp (congrArg Subtype.val ha))
  · intro ha
    exact Subtype.ext (h.mpr (congrArg Subtype.val ha))

/-- The two faithful integral Hecke algebras, with the same original prime-word values. -/
def originalLatticeCuspHeckeEquiv {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    originalFullLatticeHeckeAlgebra N b ≃+* sourceOriginalIntegralHeckeAlgebra N 2 :=
  commonHeckeWordRingEquiv (originalFullLatticeHeckeWord N b).toRingHom
    (sourceIntegralCuspHeckeWord N).toRingHom (originalFullLatticeHeckeWord_surjective N b)
    (sourceIntegralCuspHeckeWord_surjective N) (originalLatticeCuspHecke_same_relations N b)

theorem originalLatticeCuspHeckeEquiv_word {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalLatticeCuspHeckeEquiv N b (originalFullLatticeHeckeWord N b a) =
      sourceIntegralCuspHeckeWord N a :=
  commonHeckeWordRingEquiv_apply (originalFullLatticeHeckeWord N b).toRingHom
    (sourceIntegralCuspHeckeWord N).toRingHom (originalFullLatticeHeckeWord_surjective N b)
    (sourceIntegralCuspHeckeWord_surjective N) (originalLatticeCuspHecke_same_relations N b) a

theorem originalLatticeCuspHeckeEquiv_prime {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (ell : Nat.Primes) :
    (originalLatticeCuspHeckeEquiv N b
      (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))).val = cuspHeckeLinear N 2 ell.val :=
  (congrArg Subtype.val (originalLatticeCuspHeckeEquiv_word N b (FreeAlgebra.ι ℤ ell))).trans
    (sourceIntegralCuspHeckeWord_prime N ell)

end
end Dubon2026.SourceFunctionField.OriginalChart
