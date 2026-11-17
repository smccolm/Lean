import Dubon2026.SourceMarkedOriginalNormalField
import Dubon2026.SourceEllipticCharTwoInertiaSign
import Dubon2026.SourceNormalFieldCoordinateOrder

/-! DUB-17/18 -> reverse original genus -> characteristic-two wild
different. The native order-twelve inertia quotient and original marked
chart construct a normal auxiliary field containing the original Gamma1
field. Every positive j order in that field divides twelve. This removes
the auxiliary-field premise of the required order-twelve/fourteen bound. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup SourceCurve SourceEllipticCharTwo
open GammaOne GammaOne.ToricCoordinates IntegralDiamond
attribute [local instance] charTwoSignSubgroup_normal
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
    [CharP (IsLocalRing.ResidueField A) 2]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem exists_original_normal_field_j_order_dvd_twelve
    (h2N : ¬ 2 ∣ N) (hN : 2 ≤ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk) :
    let Ω := AlgebraicClosure (RatFunc kk)
    ∃ M : IntermediateField (RatFunc kk) Ω,
      letI : Algebra kk M := IntermediateField.algebra' M
      ∃ L : IntermediateField (RatFunc kk) M,
        letI : Algebra kk L := IntermediateField.algebra' L
        FiniteDimensional (RatFunc kk) L ∧ IsGalois (RatFunc kk) L ∧
        ∃ ι : F →ₐ[kk] L, ι x = algebraMap (RatFunc kk) L RatFunc.X ∧
          ∀ v : Place kk L, 0 < v.ord (algebraMap (RatFunc kk) L RatFunc.X) →
            v.ord (algebraMap (RatFunc kk) L RatFunc.X) ∣ (12 : ℤ) := by
  classical
  letI := valuation_residue_isAlgClosed A
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNK : (N : kk) ≠ 0 := fun h => h2N ((CharP.cast_eq_zero_iff kk 2 N).mp h)
  let Ω := AlgebraicClosure (RatFunc kk)
  letI : Algebra kk Ω := inferInstanceAs (Algebra kk (AlgebraicClosure (RatFunc kk)))
  letI : IsScalarTower kk (RatFunc kk) Ω :=
    inferInstanceAs (IsScalarTower kk (RatFunc kk) (AlgebraicClosure (RatFunc kk)))
  obtain ⟨M, hfd, hgal, hfull, w, π, hw, hcard, hker⟩ :=
    SourceEllipticDivisionField.exists_char_two_exceptional_inertia_sign kk Ω N hNK
  letI : Algebra kk M := IntermediateField.algebra' M
  letI : IsScalarTower kk (RatFunc kk) M := IntermediateField.isScalarTower M
  letI := hfd
  letI := hgal
  obtain ⟨L, hfdL, hgalL, ι, hι, hfix⟩ :=
    exists_original_normal_field_of_torsion_sign_kernel A N 2 h2N hN x hx
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
