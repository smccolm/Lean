import Dubon2026.SourceCurveNormFiber
import Dubon2026.SourceConstantFieldOrderResidues
import Mathlib.Algebra.Ring.GeomSum

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
unramified cover genus. Existing norm-fiber orders give the local upper
bound, and the actual geometric sum is a unit when the root and its
nonzero constant residue agree. Adapted from the OrdNorm and ResidueGeomSum
arguments in anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.
No evaluation map or additional residue-field package is introduced. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing

theorem ord_le_ord_norm_of_nonnegative_fiber
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]
    (w : Place K E)
    (hbase : Function.Bijective (algebraMap K (w.restrict F).ResidueField))
    (htop : ∀ v : Place K E, Function.Bijective (algebraMap K v.ResidueField))
    {x : E} (hx : x ≠ 0)
    (hnonneg : ∀ v : Place K E, v.restrict F = w.restrict F → 0 ≤ v.ord x) :
    w.ord x ≤ (w.restrict F).ord (Algebra.norm F x) := by
  classical
  haveI := finite_placeFiber (E := E) (w.restrict F)
  letI := Fintype.ofFinite {v : Place K E // v.restrict F = w.restrict F}
  rw [ord_norm_eq_sum_fiber (w.restrict F) hbase htop hx, finsum_eq_sum_of_fintype]
  let i : {v : Place K E // v.restrict F = w.restrict F} := ⟨w, rfl⟩
  have hsum := Finset.single_le_sum (s := Finset.univ) (a := i)
    (f := fun v : {v : Place K E // v.restrict F = w.restrict F} => v.1.ord x)
    (fun v _ => hnonneg v.1 v.2) (Finset.mem_univ i)
  exact hsum

theorem ord_pow_sub_constant_of_same_residue
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    (w : Place K F) {x : F} (hx : x ∈ w.toValuationSubring)
    {c : K} (hc : c ≠ 0)
    (hres : residue w.toValuationSubring ⟨x, hx⟩ = algebraMap K w.ResidueField c)
    (hne : x - algebraMap K F c ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    w.ord (x ^ n - (algebraMap K F c) ^ n) = w.ord (x - algebraMap K F c) := by
  haveI : CharZero w.ResidueField :=
    (RingHom.charZero_iff (algebraMap K w.ResidueField).injective).mp ‹CharZero K›
  let X : w.toValuationSubring := ⟨x, hx⟩
  let C : w.toValuationSubring := algebraMap K w.toValuationSubring c
  let S : w.toValuationSubring := ∑ j ∈ Finset.range n, X ^ j * C ^ (n - 1 - j)
  have hC : residue w.toValuationSubring C = algebraMap K w.ResidueField c :=
    (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField c).symm
  have hS : residue w.toValuationSubring S =
      (n : w.ResidueField) * (algebraMap K w.ResidueField c) ^ (n - 1) := by
    dsimp only [S]
    rw [map_sum]
    simp only [map_mul, map_pow, show residue w.toValuationSubring X =
      algebraMap K w.ResidueField c from hres, hC]
    exact geom_sum₂_self _ n
  have hSu : IsUnit S := (residue_ne_zero_iff_isUnit S).mp (by
    rw [hS]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn)
      (pow_ne_zero _ ((map_ne_zero _).mpr hc)))
  have hS0 : (S : F) ≠ 0 := fun h => hSu.ne_zero (Subtype.ext h)
  have hfact : x ^ n - (algebraMap K F c) ^ n = (x - algebraMap K F c) * (S : F) := by
    have h := ((Commute.all X C).mul_geom_sum₂ n).symm
    have hh := congrArg (fun a : w.toValuationSubring => (a : F)) h
    exact hh
  rw [hfact, w.ord_mul hne hS0, ConstantField.ord_coe_isUnit w hSu, add_zero]

end
end Dubon2026.SourceCurve.Place
