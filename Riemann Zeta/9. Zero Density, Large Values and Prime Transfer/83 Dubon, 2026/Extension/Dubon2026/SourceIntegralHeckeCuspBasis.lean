import Dubon2026.SourceIntegralHeckeBasisCoordinates
import Dubon2026.SourceWeightTwoCuspHeckeDual

/-! DUB-17/18 -> rank-two Hecke descent -> rational cusp matrices.
Dualizing the actual integral algebra basis through the proved perfect
coefficient pairing gives cusp forms on which every integral Hecke
operator has an integer matrix. No integral Fourier-structure premise
or prescribed rational basis is assumed.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2
local notation "S" => CuspForm (Gamma0 N) 2

/-- Cusp forms dual to the genuine integral Hecke basis under first-coefficient evaluation. -/
def sourceIntegralHeckeCuspBasis {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι ℤ TZ) :
    Module.Basis ι ℂ S :=
  (sourceIntegralHeckeComplexBasis N b).dualBasis.map
    (sourceWeightTwoCuspHeckeDualEquiv N).symm

theorem sourceIntegralHeckeCuspBasis_repr {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι ℤ TZ) (f : S) (i : ι) :
    (sourceIntegralHeckeCuspBasis N b).repr f i =
      sourceWeightTwoCuspHeckeDualEquiv N f (sourceIntegralHeckeComplexBasis N b i) := by
  change (sourceIntegralHeckeComplexBasis N b).dualBasis.repr
    (sourceWeightTwoCuspHeckeDualEquiv N f) i = _
  exact Module.Basis.dualBasis_repr _ _ _

theorem sourceIntegralHeckeCuspBasis_pairing {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι ℤ TZ) (i : ι) :
    sourceWeightTwoCuspHeckeDualEquiv N (sourceIntegralHeckeCuspBasis N b i) =
      (sourceIntegralHeckeComplexBasis N b).dualBasis i := by
  simp [sourceIntegralHeckeCuspBasis]

theorem sourceIntegralHeckeCuspBasis_operator {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℤ TZ) (t : TZ) (i j : ι) :
    (sourceIntegralHeckeCuspBasis N b).repr (t.val (sourceIntegralHeckeCuspBasis N b i)) j =
      (b.repr (b j * t) i : ℂ) := by
  rw [sourceIntegralHeckeCuspBasis_repr]
  change sourceWeightTwoCuspHeckeDualEquiv N
    ((sourceIntegralHeckeToComplex N t).val (sourceIntegralHeckeCuspBasis N b i)) _ = _
  rw [sourceWeightTwoCuspHeckeDualEquiv_operator, sourceIntegralHeckeCuspBasis_pairing,
    Module.Basis.dualBasis_apply, ← sourceIntegralHeckeToComplex_basis N b j,
    ← map_mul, sourceIntegralHeckeComplexBasis_repr]

/-- A constructed finite cusp basis with integral matrices for all actual Hecke operators. -/
def sourceRationalHeckeCuspBasis :
    Module.Basis (Fin (Module.finrank ℤ TZ)) ℂ S :=
  sourceIntegralHeckeCuspBasis N (sourceIntegralHeckeBasis N)

theorem sourceRationalHeckeCuspBasis_integral (n : ℕ+)
    (i j : Fin (Module.finrank ℤ TZ)) :
    ∃ z : ℤ, (sourceRationalHeckeCuspBasis N).repr
      (cuspHeckeLinear N 2 (n : ℕ) (sourceRationalHeckeCuspBasis N i)) j = (z : ℂ) := by
  let t : TZ := ⟨cuspHeckeLinear N 2 (n : ℕ), Algebra.subset_adjoin ⟨n, rfl⟩⟩
  exact ⟨(sourceIntegralHeckeBasis N).repr (sourceIntegralHeckeBasis N j * t) i,
    sourceIntegralHeckeCuspBasis_operator N (sourceIntegralHeckeBasis N) t i j⟩

theorem sourceRationalHeckeCuspBasis_rational (n : ℕ+)
    (i j : Fin (Module.finrank ℤ TZ)) :
    (sourceRationalHeckeCuspBasis N).repr
      (cuspHeckeLinear N 2 (n : ℕ) (sourceRationalHeckeCuspBasis N i)) j ∈
        Set.range ((↑) : ℚ → ℂ) := by
  obtain ⟨z, hz⟩ := sourceRationalHeckeCuspBasis_integral N n i j
  exact ⟨(z : ℚ), by simpa using hz.symm⟩

end
end Dubon2026
