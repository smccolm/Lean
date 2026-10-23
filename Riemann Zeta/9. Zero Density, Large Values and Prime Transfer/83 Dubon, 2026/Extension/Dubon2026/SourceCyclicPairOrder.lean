import Dubon2026.SourceEllipticTorsionStructure
import Dubon2026.SourceLevelIndexFormula

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual number of cyclic subgroups. Reuse the already proved
projective-line cardinality and Dedekind psi function without redefining
either. Primitive pairs use native IsCoprime. The actual torsion structure
transports these subgroups into the original elliptic point group.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean and
S_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean. -/
namespace Dubon2026.SourceEllipticCyclicCount
open AddSubgroup Dubon2026.SourceLevelProjective
noncomputable section
variable (N : ℕ)

private theorem nsmul_eq_zero_of_dvd_mul_val {m : ℕ} {z : ZMod N} [NeZero N]
    (h : N ∣ m * z.val) : m • z = 0 :=
  calc m • z = (m : ZMod N) * z := nsmul_eq_mul m z
    _ = (m : ZMod N) * (z.val : ZMod N) := by rw [ZMod.natCast_zmod_val]
    _ = ((m * z.val : ℕ) : ZMod N) := (Nat.cast_mul _ _).symm
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h

variable [NeZero N]

omit [NeZero N] in

theorem coprime_addOrderOf_eq {a c : ZMod N} (h : IsCoprime a c) :
    addOrderOf ((a, c) : ZMod N × ZMod N) = N := by
  obtain ⟨x, y, hxy⟩ := h

  have hdvdN : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N := by
    refine addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
    rw [Prod.smul_mk]
    have hza : N • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hzc : N • c = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hza, hzc]
    rfl

  have hN : N ∣ addOrderOf ((a, c) : ZMod N × ZMod N) := by
    have hsmul : addOrderOf ((a, c) : ZMod N × ZMod N) • ((a, c) : ZMod N × ZMod N) = 0 :=
      addOrderOf_nsmul_eq_zero _
    rw [Prod.smul_mk] at hsmul
    have ha : addOrderOf ((a, c) : ZMod N × ZMod N) • a = 0 := congrArg Prod.fst hsmul
    have hc : addOrderOf ((a, c) : ZMod N × ZMod N) • c = 0 := congrArg Prod.snd hsmul
    rw [nsmul_eq_mul] at ha hc
    have hzero : ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N) = 0 := by
      calc ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N)
          = (addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * (x * a + y * c) := by
            rw [hxy, mul_one]
        _ = x * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * a)
              + y * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * c) := by ring
        _ = 0 := by rw [ha, hc, mul_zero, mul_zero, add_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact Nat.dvd_antisymm hdvdN hN

theorem isCoprime_of_addOrderOf_eq {a c : ZMod N}
    (h : addOrderOf ((a, c) : ZMod N × ZMod N) = N) : IsCoprime a c := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set d : ℕ := Nat.gcd (Nat.gcd a.val c.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hdA : d ∣ a.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hdC : d ∣ c.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

  have hd1 : d = 1 := by
    have hkill : (N / d) • ((a, c) : ZMod N × ZMod N) = 0 := by
      rw [Prod.smul_mk]
      have hka : (N / d) • a = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨A', hA'⟩ := hdA
        exact ⟨A', by rw [hA', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      have hkc : (N / d) • c = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨C', hC'⟩ := hdC
        exact ⟨C', by rw [hC', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      rw [hka, hkc]
      rfl
    have horder : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N / d :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    rw [h] at horder
    have hdivdvd : N / d ∣ N := Nat.div_dvd_of_dvd hdN
    have hNd : N / d = N := Nat.dvd_antisymm hdivdvd horder
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdN
    rw [hNd] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) (hmul.trans (one_mul N).symm)

  have hcop : Nat.Coprime (Nat.gcd a.val c.val) N := hd1
  have hunit : IsUnit ((Nat.gcd a.val c.val : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ N).mpr hcop
  obtain ⟨u, hu⟩ := hunit
  have hbez := Nat.gcd_eq_gcd_ab a.val c.val
  have hcast : ((Nat.gcd a.val c.val : ℕ) : ZMod N)
      = a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N) + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N) := by
    have hℤ := congrArg (fun z : ℤ => (Int.castRingHom (ZMod N)) z) hbez
    simp only [map_add, map_mul, Int.coe_castRingHom] at hℤ
    rw [Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at hℤ
    exact hℤ
  refine ⟨((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N),
    ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N), ?_⟩
  calc ((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * a
        + ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * c
      = (a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N)
          + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N)) * (↑u⁻¹ : ZMod N) := by ring
    _ = ((Nat.gcd a.val c.val : ℕ) : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [← hcast]
    _ = (↑u : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [hu]
    _ = 1 := u.mul_inv


end
end Dubon2026.SourceEllipticCyclicCount
