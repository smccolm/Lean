import Dubon2026.AdicPowerQuotientTopology
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.Group.Basic

/-! # The actual original matrix group in the product of its power quotients -/

namespace Dubon2026

noncomputable section
open Matrix

variable {R ι : Type*} [CommRing R] [WithIdeal R] [Fintype ι] [DecidableEq ι]

/-- The whole original matrix is sent to all of its genuine power-quotient reductions. -/
def adicMatrixReductionProduct : GeneralLinearGroup ι R →*
    ((n : ℕ) → GeneralLinearGroup ι (R ⧸ (WithIdeal.i : Ideal R) ^ n)) :=
  Pi.monoidHom fun n => GeneralLinearGroup.map
    (n := ι) (R := R) (S := R ⧸ (WithIdeal.i : Ideal R) ^ n)
    (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))

/-- Every original quotient coordinate of the genuine reduction product is continuous. -/
theorem adicMatrixReductionProduct_continuous :
    Continuous (adicMatrixReductionProduct (R := R) (ι := ι)) :=
  continuous_pi fun n => adicMatrixPowerReduction_continuous n

/-- Genuine adic separatedness recovers each original matrix from all of its actual quotient reductions. -/
theorem adicMatrixReductionProduct_injective [T2Space R] :
    Function.Injective (adicMatrixReductionProduct (R := R) (ι := ι)) := by
  letI : IsHausdorff (WithIdeal.i : Ideal R) R :=
    (IsAdic.isHausdorff_iff (I := (WithIdeal.i : Ideal R)) rfl).mpr inferInstance
  intro u v h
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply (IsHausdorff.eq_iff_smodEq (I := (WithIdeal.i : Ideal R))).mpr
  intro n
  rw [SModEq.sub_mem]
  change u.val i j - v.val i j ∈ ((WithIdeal.i : Ideal R) ^ n • (⊤ : Ideal R))
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  apply Ideal.Quotient.eq.mp
  exact congrArg
    (fun a : GeneralLinearGroup ι (R ⧸ (WithIdeal.i : Ideal R) ^ n) => a.val i j)
    (congrFun h n)

/-- Compactness makes the actual original matrix reduction product a closed topological embedding. -/
theorem adicMatrixReductionProduct_isClosedEmbedding [T2Space R] [CompactSpace R] :
    Topology.IsClosedEmbedding (adicMatrixReductionProduct (R := R) (ι := ι)) := by
  letI : CompactSpace (Matrix ι ι R) := inferInstanceAs (CompactSpace (ι → ι → R))
  letI : ∀ n : ℕ, DiscreteTopology (R ⧸ (WithIdeal.i : Ideal R) ^ n) :=
    fun n => adicPowerQuotient_discrete n
  exact adicMatrixReductionProduct_continuous.isClosedEmbedding
    adicMatrixReductionProduct_injective

/-- The literal matrix reduction kernels decrease with the original adic power. -/
theorem adicMatrixPowerReduction_kernel_antitone :
    Antitone (fun n : ℕ =>
      (GeneralLinearGroup.map (n := ι) (R := R)
        (S := R ⧸ (WithIdeal.i : Ideal R) ^ n)
        (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))).ker) := by
  intro m n hmn u hu
  let q := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := (WithIdeal.i : Ideal R)) hmn)
  have hcomm : Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ m) =
      q.comp (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n)) := by
    ext x
    rfl
  change GeneralLinearGroup.map (n := ι)
    (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ m)) u = 1
  rw [hcomm, GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
  rw [show GeneralLinearGroup.map (n := ι)
    (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n)) u = 1 from hu, map_one]

end
end Dubon2026
