import Dubon2026.SourceMarkedOriginalNormalField
import Dubon2026.SourceEllipticCharThreeInertiaPermutationR2
import Dubon2026.SourceNormalFieldCoordinateOrder

/-! DUB-17/18 -> reverse original genus -> characteristic-three wild
different. The native order-six inertia quotient and original marked
chart construct a normal auxiliary field containing the original Gamma1
field. Every positive j order in that field divides six. This removes
the auxiliary-field premise of the required order-six/seven bound. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup SourceCurve SourceEllipticExceptional
open GammaOne GammaOne.ToricCoordinates IntegralDiamond
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
    [CharP (IsLocalRing.ResidueField A) 3]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem exists_original_normal_field_j_order_dvd_six
    (h3N : ¬ 3 ∣ N) (hN : 2 ≤ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk) :
    let Ω := AlgebraicClosure (RatFunc kk)
    ∃ M : IntermediateField (RatFunc kk) Ω,
      letI : Algebra kk M := IntermediateField.algebra' M
      ∃ L : IntermediateField (RatFunc kk) M,
        letI : Algebra kk L := IntermediateField.algebra' L
        FiniteDimensional (RatFunc kk) L ∧ IsGalois (RatFunc kk) L ∧
        ∃ ι : F →ₐ[kk] L, ι x = algebraMap (RatFunc kk) L RatFunc.X ∧
          ∀ v : Place kk L, 0 < v.ord (algebraMap (RatFunc kk) L RatFunc.X) →
            v.ord (algebraMap (RatFunc kk) L RatFunc.X) ∣ (6 : ℤ) := by
  classical
  letI := valuation_residue_isAlgClosed A
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNK : (N : kk) ≠ 0 := fun h => h3N ((CharP.cast_eq_zero_iff kk 3 N).mp h)
  let Ω := AlgebraicClosure (RatFunc kk)
  letI : Algebra kk Ω := inferInstanceAs (Algebra kk (AlgebraicClosure (RatFunc kk)))
  letI : IsScalarTower kk (RatFunc kk) Ω :=
    inferInstanceAs (IsScalarTower kk (RatFunc kk) (AlgebraicClosure (RatFunc kk)))
  letI : (EA (-1 : kk)).IsElliptic := isElliptic_EA_neg_one_of_char_three
  obtain ⟨M, hfd, hgal, hfull, w, _, _, _, _, _, _, _, _, _, _, π, _,
    hwj, _, _, _, _, _, _, _, _, hcard, hker, _⟩ :=
    SourceEllipticDivisionField.exists_char_three_exceptional_inertia_permutation kk Ω N hNK
  letI : Algebra kk M := IntermediateField.algebra' M
  letI : IsScalarTower kk (RatFunc kk) M := IntermediateField.isScalarTower M
  letI := hfd
  letI := hgal
  have hw : 0 < w.ord (algebraMap (RatFunc kk) M RatFunc.X) := by
    simpa only [EA_neg_one_j_of_char_three, map_zero, sub_zero] using hwj
  obtain ⟨L, hfdL, hgalL, ι, hι, hfix⟩ :=
    exists_original_normal_field_of_torsion_sign_kernel A N 3 h3N hN x hx
      M hfull w.toValuationSubring π hker
  letI : Algebra kk L := IntermediateField.algebra' L
  letI := hfdL
  letI := hgalL
  refine ⟨M, L, hfdL, hgalL, ι, hι, ?_⟩
  intro v hv
  simpa only [hcard, Nat.cast_ofNat] using
    Place.normal_coordinate_order_dvd_of_inertia_kernel L w hw π hfix v hv

end
end Dubon2026.SourceFunctionField.MarkedChart
