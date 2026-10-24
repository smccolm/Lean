import Dubon2026.SourceJointChartFullBasis

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap -> integral
coordinate representations. Polynomial coefficients of an integral linear
combination of the lifted chart basis lie in the coefficient valuation
ring. Expand only finitely many coordinate powers and reuse the proved
joint residue coefficient criterion, without a new normalization argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem coeff_mem_of_polynomial_sum_integral
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (z : J → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (huniq : ∀ q q' : J → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q')
    (p : J → L[X]) (hp : ∀ i, ∑ j, aeval f (p j) * z j ∈ (R i).integers) :
    ∀ j n, (p j).coeff n ∈ A := by
  classical
  let v : ℕ × J → F := fun u => f ^ u.1 * z u.2
  have hv : ∀ u i, v u ∈ (R i).integers :=
    fun u i => mul_mem (pow_mem (hf i) _) (hz u.2 i)
  have hr : Joint.jointRes R v hv =
      (fun u : ℕ × J => rv R f hf ^ u.1 * rv R (z u.2) (hz u.2)) := by
    funext u i
    change (R i).residue (⟨f, hf i⟩ ^ u.1 * ⟨z u.2, hz u.2 i⟩) = _
    rw [map_mul, map_pow]
    rfl
  have hind : LinearIndependent (ResidueField A) (Joint.jointRes R v hv) := by
    rw [hr]
    exact linearIndependent_powers_of_polynomial_unique (rv R f hf)
      (fun j => rv R (z j) (hz j)) huniq
  let N := Finset.univ.sup (fun j => (p j).natDegree) + 1
  have hlt : ∀ j, (p j).natDegree < N := fun j =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j))
  have hexp : ∑ u ∈ Finset.range N ×ˢ (Finset.univ : Finset J),
      (p u.2).coeff u.1 • v u = ∑ j, aeval f (p j) * z j := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.aeval_eq_sum_range' (hlt j), Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => (smul_mul_assoc _ _ _).symm
  have hm := Joint.mem_of_sum_smul_mem_joint R v hv hind
    (Finset.range N ×ˢ (Finset.univ : Finset J)) (fun u => (p u.2).coeff u.1)
    (fun i => by rw [hexp]; exact hp i)
  intro j n
  by_cases hn : n < N
  · exact hm (n, j) (Finset.mk_mem_product (Finset.mem_range.mpr hn) (Finset.mem_univ j))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hlt j) (not_lt.mp hn))]
    exact zero_mem A

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
