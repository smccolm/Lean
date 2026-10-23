import Dubon2026.SourceOriginalLatticeCuspHeckeEquiv
import Dubon2026.SourcePrimitiveFieldHeckeCharacter

/-! DUB-17/18 -> higher symmetric-power continuation -> modular Galois
association -> specialization of the actual original Tate Hecke algebra.
The proved lattice/cusp equivalence transports the existing primitive
eigencharacter to the original lattice algebra, with its literal Fourier
values. No eigencharacter or equality of Hecke relations is supplied. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- The actual primitive eigencharacter on the original integral lattice Hecke algebra. -/
def originalLatticeEigencharacter {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (f : PrimitiveCuspForm N 2) :
    originalFullLatticeHeckeAlgebra N b →+* sourcePrimitiveCoefficientField f :=
  (sourcePrimitiveFieldHeckeCharacter f).toRingHom.comp
    (originalLatticeCuspHeckeEquiv N b).toRingHom

theorem originalLatticeEigencharacter_prime {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (f : PrimitiveCuspForm N 2) (ell : Nat.Primes) :
    originalLatticeEigencharacter N b f
      (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell)) =
        sourcePrimitiveFieldCoefficient f ell.val := by
  have he : originalLatticeCuspHeckeEquiv N b
      (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell)) =
      ⟨cuspHeckeLinear N 2 ell.val,
        Algebra.subset_adjoin ⟨⟨ell.val, ell.property.pos⟩, rfl⟩⟩ :=
    Subtype.ext (originalLatticeCuspHeckeEquiv_prime N b ell)
  exact (congrArg (sourcePrimitiveFieldHeckeCharacter f) he).trans
    (sourcePrimitiveFieldHeckeCharacter_hecke f ⟨ell.val, ell.property.pos⟩)

theorem originalLatticeEigencharacter_isIntegral {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (f : PrimitiveCuspForm N 2)
    (t : originalFullLatticeHeckeAlgebra N b) :
    IsIntegral ℤ (originalLatticeEigencharacter N b f t) :=
  sourcePrimitiveFieldHeckeCharacter_isIntegral f (by norm_num)
    (originalLatticeCuspHeckeEquiv N b t)

end
end Dubon2026.SourceFunctionField.OriginalChart
