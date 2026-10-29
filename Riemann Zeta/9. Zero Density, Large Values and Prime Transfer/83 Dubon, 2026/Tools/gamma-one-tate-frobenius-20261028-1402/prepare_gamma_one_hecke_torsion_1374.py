from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('SourceGammaOneHeckeTorsionDivisors1374a.lean','''import SourceGammaOneHeckeIntegralAgreement1373a

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> Hecke compatibility
on finite torsion. Native primitive constant normalization makes every
principal divisor an actual Gauss-unit principal divisor. A torsion class
has a principal nonzero multiple; cancellation in the integer divisor group
then gives the exact correspondence on that class's divisor representative.
No upper-curve good-reduction model or global Picard divisibility is needed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField CongruenceSubgroup ConstantField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M p : ℕ) [NeZero M] [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField A) p]
local notation "Γ" => Gamma1 M
local notation "FF" => functionFieldOver Γ Qbar
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem exists_gammaOne_hecke_reduction_torsion_divisor_of_degree_eq
    (hcop : Nat.Coprime M p)
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p) :
    ∃ g : Gamma0 M, (p : ZMod M) * (g.val 1 1 : ZMod M) = 1 ∧
      ∀ (R : ConstantReduction A FF Fb), R.toRegularProlongation = regularProlongation A Γ →
        ∀ (D : Divisor.degZero (K := Qbar) (F := FF)) (m : ℕ), m ≠ 0 → m • Pic0.mk D = 0 →
          R.divMap (heckeDivisor Qbar M p D.val) =
            decompositionResidueDivisorEquiv A Γ d
              (R.divMap (fieldDivisorEquiv (arithmeticDiamondAut M g) D.val)) +
            p • (decompositionResidueDivisorEquiv A Γ d).symm (R.divMap D.val) := by
  obtain ⟨g, hlabel, hint⟩ :=
    exists_gammaOne_hecke_reduction_integral_principal_of_degree_eq A M p hcop hdeg d hd
  refine ⟨g, hlabel, fun R hR D m hm hD => ?_⟩
  let T : Divisor Qbar FF →+ Divisor kk Fb := R.divMap.comp (heckeDivisor Qbar M p)
  let S : Divisor Qbar FF →+ Divisor kk Fb :=
    (decompositionResidueDivisorEquiv A Γ d).toAddMonoidHom.comp
      (R.divMap.comp (fieldDivisorEquiv (arithmeticDiamondAut M g)).toAddMonoidHom) +
    p • ((decompositionResidueDivisorEquiv A Γ d).symm.toAddMonoidHom.comp R.divMap)
  have hp : Divisor.IsPrincipal (m • D.val) :=
    (Pic0.mk_mem_torsion_iff D m).mp (Pic0.mem_torsion_iff.mpr hD)
  obtain ⟨f, hf, hDf⟩ := hp
  obtain ⟨c, hc, hres⟩ := (regularProlongation A Γ).exists_smul_mem f hf
  have hc0 : c ≠ 0 := by
    intro hz
    subst c
    have he : (⟨(0 : Qbar) • f, hc⟩ : (regularProlongation A Γ).integers) = 0 :=
      Subtype.ext (zero_smul Qbar f)
    exact hres (by rw [he, map_zero])
  let u : coefficientGaussRing Γ A := ⟨c • f, hc⟩
  have he : m • D.val = principalDivisor M Qbar u.val := by
    change m • D.val = principalDivisor M Qbar (c • f)
    rw [principal_smul M hc0]
    ext P
    exact hDf P
  have h := hint R hR u hres
  change T (principalDivisor M Qbar u.val) = S (principalDivisor M Qbar u.val) at h
  rw [← he, map_nsmul, map_nsmul] at h
  exact nsmul_right_injective hm h

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
out('SourceGammaOneResiduePicard1375a.lean','''import SourceGammaOneResidueDivisors1370a
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> the actual residue
Picard coefficient action. The proved place permutation preserves degree
and transports every principal order divisor, so it descends through the
native degree-zero Picard quotient. The inverse remains explicit. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem decompositionResidueDivisorEquiv_symm (d : A.decompositionSubgroup ℚ) (D : Divisor kk Fb) :
    (decompositionResidueDivisorEquiv A Γ d).symm D = decompositionResidueDivisorEquiv A Γ d⁻¹ D := by
  ext P
  change D (decompositionResiduePlace A Γ d P) = D (decompositionResiduePlace A Γ d⁻¹⁻¹ P)
  rw [inv_inv]

theorem decompositionResidueDivisor_principal (d : A.decompositionSubgroup ℚ)
    (D : Divisor kk Fb) (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (decompositionResidueDivisorEquiv A Γ d D) := by
  obtain ⟨f, hf, hD⟩ := hD
  exact ⟨decompositionResidueAut A Γ d f, (map_ne_zero _).mpr hf,
    decompositionResidueDivisorEquiv_order A Γ d D f hD⟩

variable [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

/-- The actual residue decomposition action restricted to degree-zero divisors. -/
def decompositionResidueDegZero (d : A.decompositionSubgroup ℚ) :
    Divisor.degZero (K := kk) (F := Fb) →+ Divisor.degZero (K := kk) (F := Fb) where
  toFun D := ⟨decompositionResidueDivisorEquiv A Γ d D.val, by
    change Divisor.degree (decompositionResidueDivisorEquiv A Γ d D.val) = 0
    rw [decompositionResidueDivisorEquiv_degree A Γ hT]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D E := Subtype.ext (map_add _ D.val E.val)

/-- The genuine coefficient action on the actual residue Picard quotient. -/
def decompositionResiduePicard (d : A.decompositionSubgroup ℚ) : Pic0 kk Fb →+ Pic0 kk Fb :=
  QuotientAddGroup.map _ _ (decompositionResidueDegZero A Γ hT d) (by
    intro D hD
    exact decompositionResidueDivisor_principal A Γ d D.val hD)

theorem decompositionResiduePicard_mk (d : A.decompositionSubgroup ℚ)
    (D : Divisor.degZero (K := kk) (F := Fb)) :
    decompositionResiduePicard A Γ hT d (Pic0.mk D) =
      Pic0.mk (decompositionResidueDegZero A Γ hT d D) := rfl

theorem decompositionResiduePicard_inverse (d : A.decompositionSubgroup ℚ) (x : Pic0 kk Fb) :
    decompositionResiduePicard A Γ hT d⁻¹ (decompositionResiduePicard A Γ hT d x) = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [decompositionResiduePicard_mk, decompositionResiduePicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  change decompositionResidueDivisorEquiv A Γ d⁻¹ (decompositionResidueDivisorEquiv A Γ d D.val) = D.val
  rw [← decompositionResidueDivisorEquiv_symm, AddEquiv.symm_apply_apply]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneHeckeTorsionDivisors1374a','SourceGammaOneResiduePicard1375a')")
out('build_gamma_one_hecke_torsion_1374.ps1',s)
