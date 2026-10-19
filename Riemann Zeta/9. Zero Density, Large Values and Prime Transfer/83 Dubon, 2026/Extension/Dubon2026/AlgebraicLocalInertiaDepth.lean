import Dubon2026.LocalResidueRootSeparation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! Arbitrarily deep finite quotients of the original local inertia quotient.
Roots of unity in the original closure and their open Krull stabilizers
discharge the depth assumption of DUB-17's unramified H1 dimension theorem. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [IsSepClosed L] [CharZero L]
  [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- For each positive depth, an actual open normal subgroup detects that
depth in powers of the same original arithmetic Frobenius modulo inertia. -/
theorem algebraicLocal_exists_frobenius_depth
    (φ : Gal(L/K))
    (hφ : ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^
        Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)))
    (n : ℕ) (hn : 0 < n) :
    ∃ U : OpenNormalSubgroup Gal(L/K), ∀ j : ℕ,
      φ ^ j ∈ algebraicLocalInertia K L ⊔ U.toSubgroup → n ∣ j := by
  classical
  let q := Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))
  let R := algebraicLocalIntegerRing L
  let κ := IsLocalRing.ResidueField R
  have hq : 2 ≤ q := Finite.one_lt_card
  have hqκ : (q : κ) = 0 := algebraicLocal_residue_cast_card_eq_zero K L
  have hqn : q ≤ q ^ n := Nat.le_self_pow hn.ne' _
  have hqn1 : 1 ≤ q ^ n := by omega
  let m := q ^ n - 1
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hmκ : (m : κ) ≠ 0 := by
    rw [show m = q ^ n - 1 from rfl, Nat.cast_sub hqn1, Nat.cast_pow,
      hqκ, zero_pow hn.ne', Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  letI : NeZero (m : L) := ⟨by exact_mod_cast hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  have hζR : ζ ∈ R := by
    change ‖ζ‖₊ ≤ 1
    have he : ‖ζ‖₊ ^ m = 1 := by rw [← nnnorm_pow, hζ.pow_eq_one, nnnorm_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hm0).mp he).le
  let z : R := ⟨ζ, hζR⟩
  let r : κ := IsLocalRing.residue R z
  have hz : z ^ m = 1 := Subtype.ext hζ.pow_eq_one
  have hr : r ^ m = 1 := by change (IsLocalRing.residue R z) ^ m = 1; rw [← map_pow, hz, map_one]
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, zero_pow hm0] at hr
    exact zero_ne_one hr
  have hopen : IsOpen (MulAction.stabilizer Gal(L/K) ζ : Set Gal(L/K)) :=
    stabilizer_isOpen_of_isIntegral (K := K) ζ
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hopen (Subgroup.one_mem _)
  refine ⟨U, fun j hj => ?_⟩
  have hI : algebraicLocalInertia K L ≤ MulAction.stabilizer Gal(L/K) r := by
    intro g hg
    exact (algebraicLocalInertia_mem_iff K L g).mp hg r
  have hUr : U.toSubgroup ≤ MulAction.stabilizer Gal(L/K) r := by
    intro g hg
    change g • IsLocalRing.residue R z = IsLocalRing.residue R z
    rw [← IsLocalRing.ResidueField.residue_smul]
    congr 1
    apply Subtype.ext
    exact hU hg
  have hfix : r ^ (q ^ j) = r := by
    have he := (sup_le hI hUr) hj
    change φ ^ j • r = r at he
    rwa [algebraicLocal_frobenius_pow_residue K L φ q hφ] at he
  have hj1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  have hres : IsLocalRing.residue R (z ^ (q ^ j - 1)) = 1 := by
    rw [map_pow]
    apply mul_right_cancel₀ hr0
    change r ^ (q ^ j - 1) * r = 1 * r
    rw [← pow_succ, Nat.sub_add_cancel hj1, one_mul]
    exact hfix
  have hpow : (z ^ (q ^ j - 1)) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have he := local_eq_one_of_residue_eq_one_of_pow_eq_one hpow hmκ hres
  have hd : m ∣ q ^ j - 1 := by
    rw [← hζ.pow_eq_one_iff_dvd]
    exact congrArg Subtype.val he
  exact local_exponent_dvd_of_pow_sub_one_dvd hq hd

/-- The actual local quotient by inertia admits finite open quotients of
orders divisible by every prescribed positive integer. -/
theorem algebraicLocal_exists_inertia_quotient_card_dvd (n : ℕ) (hn : 0 < n) :
    ∃ U : OpenNormalSubgroup Gal(L/K),
      n ∣ Nat.card (Gal(L/K) ⧸ (algebraicLocalInertia K L ⊔ U.toSubgroup)) := by
  obtain ⟨φ, hφ⟩ := algebraicLocal_exists_residueFrobenius K L
  obtain ⟨U, hU⟩ := algebraicLocal_exists_frobenius_depth K L φ hφ n hn
  refine ⟨U, hU _ ?_⟩
  let N := algebraicLocalInertia K L ⊔ U.toSubgroup
  have hN : IsOpen (N : Set Gal(L/K)) := Subgroup.isOpen_mono le_sup_right U.isOpen
  letI : Finite (Gal(L/K) ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have he := pow_card_eq_one' (x := (QuotientGroup.mk φ : Gal(L/K) ⧸ N))
  change (QuotientGroup.mk' N φ) ^ Nat.card (Gal(L/K) ⧸ N) = 1 at he
  rw [← map_pow (QuotientGroup.mk' N)] at he
  exact (QuotientGroup.eq_one_iff _).mp he

end
end Dubon2026
