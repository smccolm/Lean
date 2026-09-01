import GafniTao.FordPrimePowerLifts

/-!
# Ford Lemma 3.2: the exact resolved `B*` cardinality bound

After the last `d` coordinates are fixed, each source congruence has a finite
family of lifts to modulus `p^r`; after those lifts are fixed, Ford Lemma 2.4
bounds the nonsingular head fiber.  The dependent sigma type below preserves
that exact order of choices.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordBStarModulusExponent (d r : ℕ) {n : ℕ} (j : Fin n) : ℕ :=
  min (d + (j : ℕ) + 1) r

theorem fordBStarModulusExponent_pos
    {d r n : ℕ} (hdr : d < r) (j : Fin n) :
    0 < fordBStarModulusExponent d r j := by
  unfold fordBStarModulusExponent
  omega

theorem fordBStarModulusExponent_le
    {d r n : ℕ} (j : Fin n) :
    fordBStarModulusExponent d r j ≤ r := min_le_right _ _

def FordBStarLiftFamily (p d r n : ℕ) (m : ∀ j : Fin n,
    ZMod (p ^ fordBStarModulusExponent d r j)) :=
  ∀ j : Fin n,
    FordPrimePowerLiftFiber p r (fordBStarModulusExponent d r j)
      (fordBStarModulusExponent_le j) (m j)

def fordBStarLiftExponent (d r n : ℕ) : ℕ :=
  Finset.univ.sum (fun j : Fin n =>
    r - fordBStarModulusExponent d r (n := n) j)

theorem fordBStarLiftExponent_eq
    {d r k : ℕ} (hdr : d < r) (hrk : r ≤ k) :
    fordBStarLiftExponent d r (k - d) =
      (r - d - 1) * (r - d) / 2 := by
  let a := r - d - 1
  let n := k - d
  have han : a ≤ n := by
    dsimp [a, n]
    omega
  have hfirst :
      (Finset.range a).sum (fun i => r - min (d + i + 1) r) =
        a * (a + 1) / 2 := by
    calc
      (Finset.range a).sum (fun i => r - min (d + i + 1) r) =
          (Finset.range a).sum (fun i => a - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i < a := Finset.mem_range.mp hi
        rw [min_eq_left]
        · dsimp [a]
          omega
        · dsimp [a]
          omega
      _ = (Finset.range a).sum (fun i => i + 1) := by
        rw [← Finset.sum_range_reflect (fun i => i + 1) a]
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i < a := Finset.mem_range.mp hi
        omega
      _ = (Finset.range (a + 1)).sum id := by
        rw [Finset.sum_range_succ']
        simp
      _ = a * (a + 1) / 2 := by
        simp only [id_eq]
        rw [Finset.sum_range_id]
        have ha : a + 1 - 1 = a := by omega
        rw [ha, Nat.mul_comm]
  unfold fordBStarLiftExponent
  rw [Finset.sum_fin_eq_sum_range]
  simp only [fordBStarModulusExponent]
  have hguard :
      (Finset.range (k - d)).sum (fun i =>
        if h : i < k - d then r - min (d + i + 1) r else 0) =
      (Finset.range (k - d)).sum (fun i => r - min (d + i + 1) r) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  rw [hguard]
  change (Finset.range n).sum (fun i => r - min (d + i + 1) r) = _
  rw [show n = a + (n - a) by omega, Finset.sum_range_add, hfirst]
  have htail :
      (Finset.range (n - a)).sum
        (fun i => r - min (d + (a + i) + 1) r) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [min_eq_right]
    · exact Nat.sub_self r
    · dsimp [a]
      omega
  rw [htail, Nat.add_zero]
  dsimp [a]
  have ha : r - d - 1 + 1 = r - d := by omega
  rw [ha]

/-- The resolved source count: tail coordinates, compatible lifts of every
congruence target, then the nonsingular head fiber.  `target` records the
literal subtraction of the fixed tail contribution in the later source
specialization. -/
def FordResolvedBStar
    {p d r n : ℕ}
    (f : FordPrimePowerTriangularPolynomialSystem p r n)
    (m : ∀ j : Fin n, ZMod (p ^ fordBStarModulusExponent d r j))
    (target : (Fin d → ZMod (p ^ r)) → FordBStarLiftFamily p d r n m →
      Fin n → ZMod (p ^ r)) :=
  Σ tail : Fin d → ZMod (p ^ r),
    Σ lifts : FordBStarLiftFamily p d r n m,
      FordPrimePowerNonsingularTriangularFiber f (target tail lifts)

theorem fordBStarLiftFamily_card
    {p d r n : ℕ} (hp : Nat.Prime p) (hdr : d < r)
    (m : ∀ j : Fin n, ZMod (p ^ fordBStarModulusExponent d r j)) :
    Nat.card (FordBStarLiftFamily p d r n m) =
      p ^ fordBStarLiftExponent d r n := by
  classical
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  letI : Fact (1 < p ^ r) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.zero_lt_of_lt hdr).ne'⟩
  letI (j : Fin n) : Fact
      (1 < p ^ fordBStarModulusExponent d r j) :=
    ⟨one_lt_pow₀ hp.one_lt (fordBStarModulusExponent_pos hdr j).ne'⟩
  letI (j : Fin n) : Finite
      (FordPrimePowerLiftFiber p r (fordBStarModulusExponent d r j)
        (fordBStarModulusExponent_le j) (m j)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  unfold FordBStarLiftFamily
  rw [Nat.card_pi]
  simp_rw [fordPrimePowerLiftFiber_card hp
    (fordBStarModulusExponent_pos hdr _) (fordBStarModulusExponent_le _)]
  simpa [fordBStarLiftExponent] using
    (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin n))
      (fun j => r - fordBStarModulusExponent d r j) p)

theorem fordResolvedBStar_card_le
    {p d r n : ℕ} (hp : Nat.Prime p) (hr : 0 < r)
    (hdr : d < r) (hnp : n < p)
    (f : FordPrimePowerTriangularPolynomialSystem p r n)
    (m : ∀ j : Fin n, ZMod (p ^ fordBStarModulusExponent d r j))
    (target : (Fin d → ZMod (p ^ r)) → FordBStarLiftFamily p d r n m →
      Fin n → ZMod (p ^ r)) :
    Nat.card (FordResolvedBStar f m target) ≤
      n.factorial * p ^ (fordBStarLiftExponent d r n + r * d) := by
  classical
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  letI : Fact (1 < p ^ r) := ⟨one_lt_pow₀ hp.one_lt hr.ne'⟩
  letI (j : Fin n) : Fact
      (1 < p ^ fordBStarModulusExponent d r j) :=
    ⟨one_lt_pow₀ hp.one_lt (fordBStarModulusExponent_pos hdr j).ne'⟩
  letI (j : Fin n) : Finite
      (FordPrimePowerLiftFiber p r (fordBStarModulusExponent d r j)
        (fordBStarModulusExponent_le j) (m j)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (FordBStarLiftFamily p d r n m) := by
    unfold FordBStarLiftFamily
    infer_instance
  letI : Fintype (FordBStarLiftFamily p d r n m) := Fintype.ofFinite _
  letI (tail : Fin d → ZMod (p ^ r))
      (lifts : FordBStarLiftFamily p d r n m) : Finite
      (FordPrimePowerNonsingularTriangularFiber f (target tail lifts)) :=
    Finite.of_injective (fun x => x.1.1) (by
      intro x y h
      exact Subtype.ext (Subtype.ext h))
  unfold FordResolvedBStar
  rw [Nat.card_sigma]
  calc
    (∑ tail : Fin d → ZMod (p ^ r),
        Nat.card (Σ lifts : FordBStarLiftFamily p d r n m,
          FordPrimePowerNonsingularTriangularFiber f (target tail lifts))) ≤
        ∑ _tail : Fin d → ZMod (p ^ r),
          Nat.card (FordBStarLiftFamily p d r n m) * n.factorial := by
      apply Finset.sum_le_sum
      intro tail _
      rw [Nat.card_sigma]
      calc
        (∑ lifts : FordBStarLiftFamily p d r n m,
            Nat.card (FordPrimePowerNonsingularTriangularFiber
              f (target tail lifts))) ≤
            ∑ _lifts : FordBStarLiftFamily p d r n m, n.factorial :=
          Finset.sum_le_sum fun lifts _ =>
            ford_primePowerNonsingularTriangularFiber_card_le_factorial
              hp hr hnp f (target tail lifts)
        _ = Nat.card (FordBStarLiftFamily p d r n m) * n.factorial := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          change Fintype.card (FordBStarLiftFamily p d r n m) * n.factorial = _
          rw [Nat.card_eq_fintype_card]
    _ = p ^ (r * d) *
        (p ^ fordBStarLiftExponent d r n * n.factorial) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        fordBStarLiftFamily_card hp hdr m]
      simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card,
        Finset.prod_const, Finset.card_univ]
      change (p ^ r) ^ d *
        (p ^ fordBStarLiftExponent d r n * n.factorial) = _
      rw [pow_mul]
    _ = n.factorial * p ^ (fordBStarLiftExponent d r n + r * d) := by
      rw [pow_add]
      ac_rfl

#print axioms fordBStarLiftFamily_card
#print axioms fordBStarLiftExponent_eq
#print axioms fordResolvedBStar_card_le

end

end GafniTao
