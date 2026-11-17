import Dubon2026.FiniteBaseCMSymmetricDeformationRing
import Mathlib.Algebra.Ring.Commute

/-! DUB-17/18 -> actual mixed-characteristic CM deformation input. The
existing integral residual pair determines its real sign: an integral involution
has determinant one or minus one, and odd residual reduction excludes +1 in characteristic
other than two. This supplies the sign required by the native integral multiplier. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix

/-- Literal reduction of the same matrices preserves their determinant. -/
theorem original_integral_residual_determinant_map
    {O L : Type} [CommRing O] [Field L] (r : O →+* L)
    {G : Type} [Group G]
    (ρi : G →* GeneralLinearGroup (Fin 2) O)
    (ρr : G →* GeneralLinearGroup (Fin 2) L)
    (hred : ∀ g i j, (ρr g).val i j = r ((ρi g).val i j)) (g : G) :
    r (ρi g).val.det = (ρr g).val.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact (hred g i j).symm

/-- The same original integral representation is odd whenever its literal
residual representation is odd and two remains nonzero in the residue field. -/
theorem original_integral_involution_odd_of_residual
    {O L : Type} [CommRing O] [NoZeroDivisors O] [Field L] (r : O →+* L)
    (h2 : (2 : L) ≠ 0) {G : Type} [Group G]
    (ρi : G →* GeneralLinearGroup (Fin 2) O)
    (ρr : G →* GeneralLinearGroup (Fin 2) L)
    (hred : ∀ g i j, (ρr g).val i j = r ((ρi g).val i j))
    (c : G) (hc : c * c = 1) (hodd : (ρr c).val.det = -1) :
    (ρi c).val.det = -1 := by
  have hm : ρi c * ρi c = 1 := by rw [← map_mul, hc, map_one]
  have hd : (ρi c).val.det * (ρi c).val.det = 1 := by
    simpa only [Units.val_mul, Matrix.det_mul, Units.val_one, Matrix.det_one] using
      congrArg (fun A : GeneralLinearGroup (Fin 2) O => A.val.det) hm
  rcases mul_self_eq_one_iff.mp hd with hpos | hneg
  · have hr := original_integral_residual_determinant_map r ρi ρr hred c
    rw [hpos, map_one, hodd] at hr
    have hzero : (2 : L) = 0 := by
      calc
        (2 : L) = 1 + 1 := by norm_num
        _ = 0 := eq_neg_iff_add_eq_zero.mp hr
    exact (h2 hzero).elim
  · exact hneg

end
end Dubon2026.SourceDickson
