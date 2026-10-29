from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
native=['SourceOriginalHeckeIntegralAgreement','SourceOriginalTorsionDivisorAgreement','SourceOriginalHeckeTorsionReduction','SourceOriginalHeckePrincipalNorm','SourceCurveCorrespondencePrincipalOrder','SourceGammaOneHeckePicard','SourceGammaOneResidueFrobeniusPlaces','SourceGammaOneResiduePlaceOrders','SourceGammaOneDiamondPicard','SourceCurveFieldEquivPicard','SourceCurvePrincipalDivisorTransport','SourceGammaOnePrincipalDivisorIdentities']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
out('gamma-one-frobenius-divisor-route-1369.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> original all-weight arithmetic association -> original Gamma1 Picard/H1/Tate realization -> exact arithmetic Frobenius-Hecke quadratic relation.',reuse=[dict(path=str(r/(n+'.lean')),sha256=sha(r/(n+'.lean'))) for n in native],selected='The existing Gamma0 proof compares actual Hecke principal divisors via the literal norm, then uses torsion-freeness of the target integer divisor group to cancel a principal multiple. Reuse this route on original Gamma1 fields. The new Gauss norm works on all valuation integers, so native primitive constant normalization replaces the stronger coefficientwise-integral Laurent fraction decomposition. No good-reduction model of the upper Hecke correspondence is needed for this comparison.',orientation='Keep the exact field automorphism and lower-right label p*d=1 modulo M from the norm theorem. Native fieldDivisorEquiv e takes div(f) to div(e f). The existing arithmeticDiamondPicard g is defined using e.symm, so the norm term must use the inverse Picard convention or the inverse Gamma0 lift, with a proved identification. Do not silently identify the two orientations.',discharge='Actual Hecke principal norm, residue coefficient/geometric divisor order identities, and Hecke compatibility on original finite Picard torsion, leading to the literal Tate quadratic.',remaining='Actual original coordinate-degree equality and genus preservation remain. Parabolic and coefficient realization, original two-dimensional all-weight association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False),indent=2)+'\n')
out('SourceGammaOneHeckePrincipalNorm1369a.lean','''import Dubon2026.SourceCurveCorrespondencePrincipalOrder
import Dubon2026.SourceGammaOneHeckePicard
import Dubon2026.SourceGammaOnePrincipalDivisors
import Dubon2026.SourceGammaOneHeckeNormEmbeddings

/-! DUB-17/18 -> original Gamma1 Tate Frobenius quadratic -> Hecke
specialization on torsion. The actual finite divisor correspondence sends
the original principal divisor to the principal divisor of the actual alpha
norm of beta. Native ramification, residue fields and norm order suffice. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
attribute [local instance] HeckeNorm.alphaAlgebra HeckeNorm.alphaModule
variable (L : Type*) [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
local notation "FF" => laurentBaseChange L (x1FunctionField M)

theorem heckeDivisor_principal_norm (f : FF) (hf : f ≠ 0) :
    heckeDivisor L M p (principalDivisor M L f) =
      principalDivisor M L (Algebra.norm FF (heckeBeta L M p f)) := by
  ext P
  exact Divisor.geometricCorrespondence_order (heckeBeta L M p)
    (heckeAlpha L M p) (heckeBeta_finite L M p) (heckeAlpha_finite L M p)
    (gamma1_place_residue_bijective L M)
    (gamma1_hecke_place_residue_bijective L M (p * M))
    (principalDivisor M L f) f hf (fun _ => rfl) P

end
end Dubon2026.SourceFunctionField.GammaOne
''')
out('SourceGammaOneResidueDivisors1370a.lean','''import Dubon2026.SourceGammaOneResidueFrobeniusPlaces
import SourceGammaOneResidueGeometry

/-! DUB-17/18 -> original Gamma1 Hecke/Frobenius comparison on torsion ->
exact residue divisor orders. Reuse the actual decomposition place permutation
and proved geometric Frobenius ramification. The inverse permutation and
the factor p are retained exactly; no Frobenius relation is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

/-- The original residue decomposition action on actual finite divisors. -/
def decompositionResidueDivisorEquiv (d : A.decompositionSubgroup ℚ) :
    Divisor kk Fb ≃+ Divisor kk Fb := Finsupp.domCongr (decompositionResiduePlaceEquiv A Γ d)

theorem decompositionResidueDivisorEquiv_apply (d : A.decompositionSubgroup ℚ)
    (D : Divisor kk Fb) (P : Place kk Fb) :
    decompositionResidueDivisorEquiv A Γ d D (decompositionResiduePlace A Γ d P) = D P := by
  change Finsupp.equivMapDomain (decompositionResiduePlaceEquiv A Γ d) D
    (decompositionResiduePlaceEquiv A Γ d P) = D P
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem decompositionResidueDivisorEquiv_order (d : A.decompositionSubgroup ℚ)
    (D : Divisor kk Fb) (f : Fb) (hD : ∀ P, D P = P.ord f) (P : Place kk Fb) :
    decompositionResidueDivisorEquiv A Γ d D P = P.ord (decompositionResidueAut A Γ d f) := by
  obtain ⟨Q, rfl⟩ := (decompositionResiduePlaceEquiv A Γ d).surjective P
  change decompositionResidueDivisorEquiv A Γ d D (decompositionResiduePlace A Γ d Q) =
    (decompositionResiduePlace A Γ d Q).ord (decompositionResidueAut A Γ d f)
  rw [decompositionResidueDivisorEquiv_apply, decompositionResiduePlace_ord_action, hD]

theorem decompositionResidueDivisorEquiv_degree [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (d : A.decompositionSubgroup ℚ) (D : Divisor kk Fb) :
    Divisor.degree (decompositionResidueDivisorEquiv A Γ d D) = Divisor.degree D := by
  have hr (P : Place kk Fb) : Module.finrank kk P.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (residueImage_place_residue_bijective A Γ hT P)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Divisor.degree (Finsupp.equivMapDomain (decompositionResiduePlaceEquiv A Γ d)
      (Finsupp.single P n)) + _ = _
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single, hr, hr]

theorem geometricFrobenius_inverse_divisor_order (p : ℕ) [Fact p.Prime] [CharP kk p]
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p)
    (D : Divisor kk Fb) (f : Fb) (hD : ∀ P, D P = P.ord f) (P : Place kk Fb) :
    (p • (decompositionResidueDivisorEquiv A Γ d).symm D) P =
      P.ord (geometricFrobenius A Γ p d hd f) := by
  rw [Finsupp.smul_apply, nsmul_eq_mul, geometricFrobenius_place_order,
    geometricFrobeniusPlace_eq_decomposition]
  change (p : ℤ) * D (decompositionResiduePlace A Γ d P) = _
  rw [hD]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneHeckePrincipalNorm1369a','SourceGammaOneResidueDivisors1370a')")
out('build_gamma_one_frobenius_divisors_1369.ps1',s)
print('Prepared actual norm/principal and residue divisor comparisons with explicit diamond orientation.')
