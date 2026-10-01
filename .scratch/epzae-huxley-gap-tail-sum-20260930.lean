import Mathlib.Tactic
open scoped BigOperators
namespace HuxleyGapTailScratch

private theorem reciprocal_square_prefix (J : ℕ) :
    (∑ m∈Finset.range J, 1/((m:ℝ)+1)^2) ≤ 2-2/((J:ℝ)+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hstep : 1/((J:ℝ)+1)^2 ≤ 2/((J:ℝ)+1)-2/((J:ℝ)+1+1) := by
      have h₁ : (J:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (J:ℝ)+1+1 ≠ 0 := by positivity
      have he : 2/((J:ℝ)+1)-2/((J:ℝ)+1+1)=2/(((J:ℝ)+1)*((J:ℝ)+1+1)) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity : 0 < ((J:ℝ)+1)^2)
        (by positivity : 0 < ((J:ℝ)+1)*((J:ℝ)+1+1))).mpr
      nlinarith
    linarith only [ih,hstep]

private theorem finite_occupied_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (J : ℕ)
    {A B : ℝ} (hB : 0 ≤ B) (hcap : ∀ i∈S, n i ≤ J)
    (htail : ∀ m∈Finset.range J,
      ((S.filter (fun i => m < n i)).card:ℝ) ≤ A+B/((m:ℝ)+1)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(J:ℝ)+2*B := by
  classical
  have hrepr :
      (∑ m∈Finset.range J, ((S.filter (fun i => m < n i)).card:ℝ)) =
        ∑ i∈S, (n i:ℝ) := by
    calc
      _ = ∑ m∈Finset.range J, ∑ i∈S, if m < n i then (1:ℝ) else 0 := by
        simp
      _ = ∑ i∈S, ∑ m∈Finset.range J, if m < n i then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (Finset.range J).filter (fun m => m < n i)=Finset.range (n i) := by
          ext m
          simp only [Finset.mem_filter,Finset.mem_range]
          have hiCap := hcap i hi
          omega
        rw [← Finset.sum_filter,hfilter]
        simp
  rw [← hrepr]
  calc
    _ ≤ ∑ m∈Finset.range J, (A+B/((m:ℝ)+1)^2) := Finset.sum_le_sum htail
    _ = A*(J:ℝ)+B*(∑ m∈Finset.range J,1/((m:ℝ)+1)^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,div_eq_mul_inv,one_mul,Finset.mul_sum]
      ring
    _ ≤ A*(J:ℝ)+2*B := by
      have hh : (∑ m∈Finset.range J,1/((m:ℝ)+1)^2) ≤ 2 :=
        (reciprocal_square_prefix J).trans (sub_le_self _ (by positivity))
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]

private theorem finite_occupied_cubic_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    {A B K c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hc : 0 < c)
    (hcap : ∀ i∈S, (n i:ℝ)^3*c ≤ K)
    (htail : ∀ m : ℕ, 0 < m →
      ((S.filter (fun i => m ≤ n i)).card:ℝ) ≤ A+B/(m:ℝ)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(K/c)^((3:ℝ)⁻¹)+2*B := by
  classical
  let J := S.sup n
  let root := (K/c)^((3:ℝ)⁻¹)
  have hroot : 0 ≤ root := Real.rpow_nonneg (div_nonneg hK hc.le) _
  have hrootcube : root^3=K/c :=
    Real.rpow_inv_natCast_pow (div_nonneg hK hc.le) (by norm_num : (3:ℕ) ≠ 0)
  have hJcube : (J:ℝ)^3 ≤ K/c := by
    by_cases hs : S.Nonempty
    · obtain ⟨i,hi,he⟩ := Finset.sup_mem_of_nonempty (f:=n) hs
      change n i=J at he
      rw [← he]
      exact (le_div_iff₀ hc).mpr (hcap i hi)
    · have hJzero : J=0 := by simp [J,Finset.not_nonempty_iff_eq_empty.mp hs]
      rw [hJzero]
      simpa using div_nonneg hK hc.le
  have hJ : (J:ℝ) ≤ root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg J)
    hroot (by decide : (3:ℕ) ≠ 0)).mp (by rw [hrootcube]; exact hJcube)
  have hh := finite_occupied_tail_sum S n J hB (fun i hi => Finset.le_sup hi)
    (fun m _ => by
      simpa only [Nat.lt_iff_add_one_le,Nat.cast_add,Nat.cast_one] using htail (m+1) (by omega))
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hJ hA) le_rfl)

#print axioms finite_occupied_cubic_tail_sum
#print axioms reciprocal_square_prefix
#print axioms finite_occupied_tail_sum
end HuxleyGapTailScratch
