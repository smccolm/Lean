import TaoTrudgianYang2025.SargosSextupleMajorant

/-! Exact one-based source convention for finite symmetric differencing. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

def sargosSourceSequence (a : ℤ → ℂ) (M : ℕ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ioc (0:ℤ) M then a n else 0

def sargosSourceSymmetricTriple (a : ℤ → ℂ) (M H : ℕ) (m : ℤ)
    (t : SargosInitialMomentTuple H 3) : ℂ :=
  ∏ i, sargosSourceSequence a M (m+(t i:ℤ))*sargosSourceSequence a M (m-(t i:ℤ))

def sargosSourceSextupleCorrelation (a : ℤ → ℂ) (M H : ℕ) : ℝ :=
  ∑ q ∈ sargosSquareDiagonal H,
    ‖∑ m ∈ Finset.Ioc (0:ℤ) M,
      sargosSourceSymmetricTriple a M H m q.1*conj (sargosSourceSymmetricTriple a M H m q.2)‖

theorem sargos_sum_Ico_add_one {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (M : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, f (m+1)) = ∑ m ∈ Finset.Ioc (0:ℤ) M, f m := by
  apply Finset.sum_bij (fun m _ => m+1)
  · intro m hm
    have h := Finset.mem_Ico.mp hm
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  · intro m hm n hn he
    omega
  · intro n hn
    have h := Finset.mem_Ioc.mp hn
    refine ⟨n-1,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro m hm
    rfl

theorem sargosPaddedSequence_source_shift (a : ℤ → ℂ) (M : ℕ) (m : ℤ) :
    sargosPaddedSequence (fun n => a (n+1)) M m = sargosSourceSequence a M (m+1) := by
  have h : m ∈ Finset.Ico (0:ℤ) M ↔ m+1 ∈ Finset.Ioc (0:ℤ) M := by
    simp only [Finset.mem_Ico,Finset.mem_Ioc]
    omega
  simp only [sargosPaddedSequence,sargosSourceSequence,h]

theorem sargosFullSymmetricTriple_source_shift (a : ℤ → ℂ) (M H : ℕ) (m : ℤ)
    (t : SargosInitialMomentTuple H 3) :
    sargosFullSymmetricTriple (fun n => a (n+1)) M H m t =
      sargosSourceSymmetricTriple a M H (m+1) t := by
  unfold sargosFullSymmetricTriple sargosSourceSymmetricTriple
  apply Finset.prod_congr rfl
  intro i hi
  rw [sargosPaddedSequence_source_shift,sargosPaddedSequence_source_shift]
  congr 2 <;> ring

theorem sargosFullSextupleCorrelation_source_shift (a : ℤ → ℂ) (M H : ℕ) :
    sargosFullSextupleCorrelation (fun n => a (n+1)) M H =
      sargosSourceSextupleCorrelation a M H := by
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  simp_rw [sargosFullSymmetricTriple_source_shift]
  exact sargos_sum_Ico_add_one
    (fun m => sargosSourceSymmetricTriple a M H m q.1*
      conj (sargosSourceSymmetricTriple a M H m q.2)) M

theorem sargos_source_sextuple_differencing (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ‖∑ m ∈ Finset.Ioc (0:ℤ) M, a m‖^12 ≤
      1492992*((M:ℝ)/H)^6*(∑ m ∈ Finset.Ioc (0:ℤ) M, ‖a m‖^2)^6+
      (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosSourceSextupleCorrelation a M H := by
  have h := sargos_finite_sextuple_differencing (fun n => a (n+1)) hH hHM
  rw [sargos_sum_Ico_add_one,sargosFullSextupleCorrelation_source_shift] at h
  have he := sargos_sum_Ico_add_one (fun m => ‖a m‖^2) M
  rw [he] at h
  exact h

theorem sargosSourceSequence_symmetric_support (a : ℤ → ℂ) (M : ℕ)
    (m n : ℤ) (hn : 0 ≤ n) :
    sargosSourceSequence a M (m+n)*sargosSourceSequence a M (m-n) =
      if m ∈ Finset.Icc (n+1) ((M:ℤ)-n) then a (m+n)*a (m-n) else 0 := by
  by_cases hp : m+n ∈ Finset.Ioc (0:ℤ) M
  · by_cases hm : m-n ∈ Finset.Ioc (0:ℤ) M
    · have h : m ∈ Finset.Icc (n+1) ((M:ℤ)-n) := by
        simp only [Finset.mem_Ioc] at hp hm
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      simp only [sargosSourceSequence,if_pos hp,if_pos hm,if_pos h]
    · have h : m ∉ Finset.Icc (n+1) ((M:ℤ)-n) := by
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_Icc]
        omega
      simp only [sargosSourceSequence,if_pos hp,if_neg hm,if_neg h,mul_zero]
  · have h : m ∉ Finset.Icc (n+1) ((M:ℤ)-n) := by
      simp only [Finset.mem_Ioc] at hp
      simp only [Finset.mem_Icc]
      omega
    simp only [sargosSourceSequence,if_neg hp,if_neg h,zero_mul]

end TaoTrudgianYang2025
