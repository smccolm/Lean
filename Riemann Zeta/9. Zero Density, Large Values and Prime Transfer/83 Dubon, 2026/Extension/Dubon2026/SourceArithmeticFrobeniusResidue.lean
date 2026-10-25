import Dubon2026.SourceDecompositionGaussAction
import Dubon2026.SourceModularReductionPoleSpace

/-! DUB-17/18 -> original arithmetic Frobenius comparison -> actual
modular residue functions. The source Frobenius hypothesis is exactly the
native decomposition action raising each residue constant to the prime
power. The proved Gauss equivariance then identifies the actual residue
action with coefficient Frobenius. Its fixed j coordinate is retained for
the subsequent two-chart place comparison. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section

/-- Arithmetic Frobenius on the actual residue modular function field. -/
def residueArithmeticFrobenius (N : ℕ) (K : Type*) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectRing K p] :
    modularFunctionFieldCoeff N K ≃+* modularFunctionFieldCoeff N K :=
  residueCoefficientRingAut N K (frobeniusEquiv K p)

theorem residueArithmeticFrobenius_coe (N : ℕ) (K : Type*) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectRing K p] (f : modularFunctionFieldCoeff N K) :
    (residueArithmeticFrobenius N K p f : LaurentSeries K) = coeffMap (frobenius K p) f.val :=
  residueCoefficientRingAut_coe N K (frobeniusEquiv K p) f

theorem residueArithmeticFrobenius_chart (N : ℕ) (K : Type*) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectRing K p] :
    residueArithmeticFrobenius N K p (jCoeff N K) = jCoeff N K ∧
      ∀ a : K, residueArithmeticFrobenius N K p
        (algebraMap K (modularFunctionFieldCoeff N K) a) =
          algebraMap K (modularFunctionFieldCoeff N K) (a ^ p) :=
  ⟨residueCoefficientRingAut_j N K (frobeniusEquiv K p),
    fun a => residueCoefficientRingAut_constants N K (frobeniusEquiv K p) a⟩

local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueConstantsClosed

theorem original_arithmeticFrobenius_modularResidue (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] [CharP kk p] (hNk : (N : kk) ≠ 0)
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p)
    (f : gaussRing A N) :
    modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk (decompositionGaussHom A N d f) =
      residueArithmeticFrobenius N kk p (modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f) := by
  have he : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d = frobeniusEquiv kk p := by
    ext a
    exact hd a
  rw [decompositionGaussHom_modularResidue, he]
  rfl

end
end Dubon2026.SourceFunctionField.GaussReduction
