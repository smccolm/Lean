import Dubon2026.SourceGammaOneHeckeIntegralAgreement

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
