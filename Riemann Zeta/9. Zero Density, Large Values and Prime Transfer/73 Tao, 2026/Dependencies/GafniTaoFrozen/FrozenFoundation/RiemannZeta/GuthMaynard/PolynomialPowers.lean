import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Pigeonhole
import RiemannZeta.GuthMaynard.DirichletPolynomial
import Mathlib.Tactic

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard


/-- F-07: Explicitly construct convolution coefficients for the powered polynomial. -/
noncomputable def powCoeff (N k : ℕ) (m : ℕ) (T : ℝ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, detectorCoeff (p x : ℕ) T

/-- Source-faithful general factorization-count input. The constant may depend
    on `k` and `ε`, but is uniform in the positive target `m`. -/
def FactorizationCountBoundProp : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
        (fun p => (∏ x : Fin k, p x) = m)).card : ℝ) ≤ C * (m : ℝ) ^ ε

/-- Source-faithful powered-coefficient bound. Its constant may depend on `k`
    and `ε`, but is uniform in `N`, positive `m`, and `T ≥ 1`. -/
def PowCoeffBoundProp : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ (N m : ℕ) (T : ℝ),
      0 < m → 1 ≤ T → ‖powCoeff N k m T‖ ≤ C * (m : ℝ) ^ ε

lemma pow_coeff_rhs_nonneg (C : ℝ) (hC : 0 < C) (m : ℕ) (ε : ℝ) :
  0 ≤ C * (m : ℝ)^ε := by
  have h1 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ (m : ℝ) ^ ε := Real.rpow_nonneg h1 ε
  exact mul_nonneg (le_of_lt hC) h2

lemma pow_coeff_subset (N k m : ℕ) (hm : 0 < m) :
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m) ⊆
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m) := by
  intro p hp
  rw [mem_filter] at hp ⊢
  rcases hp with ⟨hp_pi, hp_prod⟩
  refine ⟨?_, hp_prod⟩
  rw [Fintype.mem_piFinset] at hp_pi ⊢
  intro x
  have hpx := hp_pi x
  rw [mem_Ioc] at hpx ⊢
  rcases hpx with ⟨hpx1, hpx2⟩
  constructor
  · by_cases hN : N = 0
    · rw [hN] at hpx1 hpx2
      linarith
    · have hN_pos : N ≥ 1 := Nat.pos_of_ne_zero hN
      linarith
  · have hdvd : p x ∣ ∏ y : Fin k, p y := dvd_prod_of_mem (fun y => p y) (mem_univ x)
    rw [hp_prod] at hdvd
    exact Nat.le_of_dvd hm hdvd

/-- F-07: The powered convolution coefficients have epsilon-power growth,
    conditionally on the two strictly narrower classical arithmetic inputs. -/
theorem powCoeff_bound_of_uniform_detector_and_factorization
    (hDetector : UniformDetectorCoeffBoundProp)
    (hFactorization : FactorizationCountBoundProp) :
    PowCoeffBoundProp := by
  intro k ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨A, hA, hDetectorA⟩ := hDetector δ hδ
  obtain ⟨B, hB, hFactorB⟩ := hFactorization k δ hδ
  refine ⟨B * A ^ k, mul_pos hB (pow_pos hA k), ?_⟩
  intro N m T hm hT
  let source := (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter
    (fun p => (∏ x : Fin k, p x) = m)
  let target := (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
    (fun p => (∏ x : Fin k, p x) = m)
  have hsource : source ⊆ target := by
    simpa [source, target] using pow_coeff_subset N k m hm
  have hterm (p : Fin k → ℕ) (hp : p ∈ source) :
      ‖∏ x : Fin k, detectorCoeff (p x) T‖ ≤ A ^ k * (m : ℝ) ^ δ := by
    rw [norm_prod]
    have hp_source := hp
    change p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter
      (fun p => (∏ x : Fin k, p x) = m) at hp_source
    rw [mem_filter] at hp_source
    rcases hp_source with ⟨hp_pi, hp_prod⟩
    rw [Fintype.mem_piFinset] at hp_pi
    calc
      ∏ x : Fin k, ‖detectorCoeff (p x) T‖
          ≤ ∏ x : Fin k, A * (p x : ℝ) ^ δ := by
            apply Finset.prod_le_prod
            · intro x _
              exact norm_nonneg _
            · intro x _
              have hpx : 0 < p x :=
                lt_of_le_of_lt (Nat.zero_le N) (mem_Ioc.mp (hp_pi x)).1
              exact hDetectorA (p x) T hpx hT
      _ = (∏ _x : Fin k, A) * (∏ x : Fin k, (p x : ℝ) ^ δ) := by
            rw [Finset.prod_mul_distrib]
      _ = A ^ k * (m : ℝ) ^ δ := by
            rw [Real.finsetProd_rpow Finset.univ (fun x => (p x : ℝ))]
            · have hp_prod_real : ∏ x : Fin k, (p x : ℝ) = (m : ℝ) := by
                exact_mod_cast hp_prod
              rw [hp_prod_real]
              simp
            · intro x _
              positivity
  rw [powCoeff]
  calc
    ‖∑ p ∈ source, ∏ x : Fin k, detectorCoeff (p x) T‖
        ≤ ∑ p ∈ source, ‖∏ x : Fin k, detectorCoeff (p x) T‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _p ∈ source, A ^ k * (m : ℝ) ^ δ := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (source.card : ℝ) * (A ^ k * (m : ℝ) ^ δ) := by simp
    _ ≤ (target.card : ℝ) * (A ^ k * (m : ℝ) ^ δ) := by
      gcongr
    _ ≤ (B * (m : ℝ) ^ δ) * (A ^ k * (m : ℝ) ^ δ) := by
      gcongr
      simpa [target] using hFactorB m hm
    _ = (B * A ^ k) * (m : ℝ) ^ ε := by
      have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
      calc
        B * (m : ℝ) ^ δ * (A ^ k * (m : ℝ) ^ δ) =
            (B * A ^ k) * ((m : ℝ) ^ δ * (m : ℝ) ^ δ) := by ring
        _ = (B * A ^ k) * (m : ℝ) ^ (δ + δ) := by
          rw [Real.rpow_add hmreal]
        _ = (B * A ^ k) * (m : ℝ) ^ ε := by
          congr 2
          dsimp [δ]
          ring

/-- The powered-coefficient bound follows from the classical divisor-count
    estimate and the source-faithful factorization-count estimate. -/
theorem powCoeff_bound_of_divisor_and_factorization
    (hDivisor : DivisorCountBoundProp)
    (hFactorization : FactorizationCountBoundProp) :
    PowCoeffBoundProp :=
  powCoeff_bound_of_uniform_detector_and_factorization
    (uniformDetectorCoeffBound_of_divisorCount hDivisor) hFactorization

/-- The powered polynomial, defined structurally as a power of the detector. -/
noncomputable def powPoly (N k : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  (detectPoly N s T) ^ k

lemma powPoly_eval (N k : ℕ) (s : ℂ) (T : ℝ) :
  powPoly N k s T = (detectPoly N s T) ^ k := by
  rfl

/-- Complex powers of a finite product of natural numbers factor coordinatewise. -/
lemma prod_natCast_cpow_eq {k : ℕ} (p : Fin k → ℕ) (s : ℂ) :
    (∏ x : Fin k, (p x : ℂ) ^ s) = ((∏ x : Fin k, p x : ℕ) : ℂ) ^ s := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- A tuple supported on `(N, 2N]` has product supported on `[N^k, (2N)^k]`.
    This includes the empty-product case `k = 0`. -/
lemma powCoeff_product_mem_support (N k : ℕ) (p : Fin k → ℕ)
    (hp : p ∈ Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))) :
    (∏ x : Fin k, p x) ∈ Finset.Icc (N ^ k) ((2 * N) ^ k) := by
  rw [Fintype.mem_piFinset] at hp
  rw [Finset.mem_Icc]
  constructor
  · calc
      N ^ k = ∏ _x : Fin k, N := by simp
      _ ≤ ∏ x : Fin k, p x := by
        apply Finset.prod_le_prod
        · intro _x _
          exact Nat.zero_le N
        · intro x _
          exact (Finset.mem_Ioc.mp (hp x)).1.le
  · calc
      ∏ x : Fin k, p x ≤ ∏ _x : Fin k, 2 * N := by
        apply Finset.prod_le_prod
        · intro x _
          exact Nat.zero_le (p x)
        · intro x _
          exact (Finset.mem_Ioc.mp (hp x)).2
      _ = (2 * N) ^ k := by simp

/-- F-07: Expanding the structural power and collecting tuples by their product
    gives exactly the explicit convolution coefficients `powCoeff`. -/
theorem polynomial_power_identity (N k : ℕ) (s : ℂ) (T : ℝ) :
    powPoly N k s T =
      ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        powCoeff N k m T * (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))
  have hsupport : ∀ p ∈ tuples,
      (∏ x : Fin k, p x) ∈ Finset.Icc (N ^ k) ((2 * N) ^ k) := by
    intro p hp
    exact powCoeff_product_mem_support N k p hp
  rw [powPoly, detectPoly, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ x : Fin k, (detectorCoeff (p x) T * (p x : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ x : Fin k, (detectorCoeff (p x) T * (p x : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ x : Fin k, detectorCoeff (p x) T) *
            ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        ∑ p ∈ tuples with (∏ x : Fin k, p x) = m,
          (∏ x : Fin k, detectorCoeff (p x) T) *
            ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        powCoeff N k m T * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [powCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

/-- A nonempty tuple supported on `(N,2N]` cannot have the artificial lower
endpoint product `N^k`. This changes the expansion support from closed-open to
the source-faithful interval `(N^k,(2N)^k]`. -/
theorem powCoeff_lower_endpoint_eq_zero (N k : ℕ) (T : ℝ)
    (hN : 0 < N) (hk : 0 < k) :
    powCoeff N k (N ^ k) T = 0 := by
  classical
  rw [powCoeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpSupport, hpProduct⟩
  rw [Fintype.mem_piFinset] at hpSupport
  have hCoordinate : ∀ x : Fin k, N + 1 ≤ p x := by
    intro x
    have hx := (Finset.mem_Ioc.mp (hpSupport x)).1
    omega
  have hProductLower : (N + 1) ^ k ≤ ∏ x : Fin k, p x := by
    calc
      (N + 1) ^ k = ∏ _x : Fin k, (N + 1) := by simp
      _ ≤ ∏ x : Fin k, p x := by
        apply Finset.prod_le_prod
        · intro _x _hx
          omega
        · intro x _hx
          exact hCoordinate x
  have hStrict : N ^ k < (N + 1) ^ k :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self N) hk.ne'
  omega

/-- The exact powered expansion with the spurious lower endpoint removed. -/
theorem polynomial_power_identity_Ioc (N k : ℕ) (s : ℂ) (T : ℝ)
    (hN : 0 < N) (hk : 0 < k) :
    powPoly N k s T =
      ∑ m ∈ Finset.Ioc (N ^ k) ((2 * N) ^ k),
        powCoeff N k m T * (m : ℂ) ^ (-s) := by
  rw [polynomial_power_identity]
  rw [Finset.Icc_eq_cons_Ioc]
  · simp [powCoeff_lower_endpoint_eq_zero N k T hN hk]
  · have hBase : N ≤ 2 * N := by omega
    exact Nat.pow_le_pow_left hBase k

/-- A wide polynomial supported on `(Q,2^k Q]`. -/
noncomputable def wideDirichletPoly (Q k : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc Q (2 ^ k * Q), a m * (m : ℂ) ^ (-t * I)

/-- The wide powered support is the disjoint union of exactly `k` ordinary
dyadic blocks. -/
theorem wideDirichletPoly_eq_sum_blocks (Q k : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    wideDirichletPoly Q k a t =
      ∑ r ∈ Finset.range k, dirichletPoly (2 ^ r * Q) a t := by
  induction k with
  | zero => simp [wideDirichletPoly]
  | succ k ih =>
      rw [wideDirichletPoly]
      have hQ : Q ≤ 2 ^ k * Q := by
        exact Nat.le_mul_of_pos_left Q (pow_pos (by omega : 0 < 2) k)
      have hBlock : 2 ^ k * Q ≤ 2 ^ (k + 1) * Q := by
        calc
          2 ^ k * Q ≤ 2 * (2 ^ k * Q) :=
            Nat.le_mul_of_pos_left (2 ^ k * Q) (by omega)
          _ = 2 ^ (k + 1) * Q := by rw [pow_succ]; ring
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hQ hBlock,
        Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
      change wideDirichletPoly Q k a t + _ = _
      rw [ih]
      rw [Finset.sum_range_succ, dirichletPoly, dyadicInterval]
      congr 1
      ring_nf

/-- One dyadic block carries at least the average of the sum of block norms. -/
theorem exists_large_dyadic_block (Q k : ℕ) (a : ℕ → ℂ) (t V : ℝ)
    (hk : 0 < k) (hV : V ≤ ‖wideDirichletPoly Q k a t‖) :
    ∃ r ∈ Finset.range k,
      V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
  have hTriangle : ‖wideDirichletPoly Q k a t‖ ≤
      ∑ r ∈ Finset.range k, ‖dirichletPoly (2 ^ r * Q) a t‖ := by
    rw [wideDirichletPoly_eq_sum_blocks]
    exact norm_sum_le _ _
  exact pigeonhole_real_sum k
    (fun r => ‖dirichletPoly (2 ^ r * Q) a t‖) V
    (hV.trans hTriangle) hk

/-- Coefficients of the powered detector after restriction to `Re s = σ`
and multiplication by the natural scale factor `(N^k)^σ`. -/
noncomputable def poweredLineCoeffs
    (N k : ℕ) (σ T : ℝ) (m : ℕ) : ℂ :=
  (((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
    (powCoeff N k m T * (m : ℂ) ^ (-(σ : ℂ)))

/-- Exact F-06/F-07 bridge: the powered fixed-line detector is a wide
Dirichlet polynomial with its coefficients normalized at the left endpoint. -/
theorem wideDirichletPoly_poweredLineCoeffs
    (N k : ℕ) (σ t T : ℝ) (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k (poweredLineCoeffs N k σ T) t =
      (((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
        powPoly N k (σ + I * t) T := by
  rw [polynomial_power_identity_Ioc N k (σ + I * t) T hN hk]
  unfold wideDirichletPoly poweredLineCoeffs
  have hUpper : 2 ^ k * N ^ k = (2 * N) ^ k := by
    rw [mul_pow]
  rw [hUpper, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Ioc] at hm
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hmNe : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hmNe]
  congr 2
  ring_nf

/-- The same identity after translating the ordinate by coefficient phase
twisting; this is the exact form consumed by the translated output of F-05. -/
theorem wideDirichletPoly_poweredLineCoeffs_translate
    (N k : ℕ) (σ T c u : ℝ) (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k
        (phaseShiftCoeffs c (poweredLineCoeffs N k σ T)) u =
      (((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
        powPoly N k (σ + I * (u + c)) T := by
  have hTranslate := wideDirichletPoly_poweredLineCoeffs N k σ (u + c) T hN hk
  simp only [wideDirichletPoly] at hTranslate ⊢
  have hCast : (((u + c : ℝ) : ℂ)) = (u : ℂ) + (c : ℂ) := by norm_num
  rw [hCast] at hTranslate
  rw [← hTranslate]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := by
    rw [Finset.mem_Ioc] at hm
    exact lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hmNe : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [phaseShiftCoeffs, if_neg hmPos.ne', mul_assoc, ← Complex.cpow_add _ _ hmNe]
  congr 2
  ring_nf

/-- Left-endpoint normalization can only decrease the norm of a powered
coefficient on the full wide support. -/
theorem norm_poweredLineCoeffs_le (N k m : ℕ) (σ T : ℝ)
    (hN : 0 < N) (hσ : 0 ≤ σ)
    (hm : m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k)) :
    ‖poweredLineCoeffs N k σ T m‖ ≤ ‖powCoeff N k m T‖ := by
  have hQNat : 0 < N ^ k := pow_pos hN k
  have hmNat : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
  have hQ : (0 : ℝ) < (N ^ k : ℕ) := by exact_mod_cast hQNat
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmNat
  have hQm : ((N ^ k : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hm).1.le
  have hPow : (((N ^ k : ℕ) : ℝ)) ^ σ ≤ (m : ℝ) ^ σ :=
    Real.rpow_le_rpow hQ.le hQm hσ
  have hmPowPos : 0 < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hmReal _
  have hScale : (((N ^ k : ℕ) : ℝ)) ^ σ * (m : ℝ) ^ (-σ) ≤ 1 := by
    rw [Real.rpow_neg (le_of_lt hmReal), ← div_eq_mul_inv]
    exact (div_le_one hmPowPos).2 hPow
  have hQNorm : ‖((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ))‖ =
      (((N ^ k : ℕ) : ℝ)) ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
    rfl
  have hmNorm : ‖((m : ℂ) ^ (-(σ : ℂ)))‖ = (m : ℝ) ^ (-σ) := by
    change ‖(((m : ℝ) : ℂ) ^ (-(σ : ℂ)))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hmReal]
    rfl
  rw [poweredLineCoeffs, norm_mul, norm_mul, hQNorm, hmNorm]
  calc
    (((N ^ k : ℕ) : ℝ)) ^ σ *
        (‖powCoeff N k m T‖ * (m : ℝ) ^ (-σ)) =
        ((((N ^ k : ℕ) : ℝ)) ^ σ * (m : ℝ) ^ (-σ)) *
          ‖powCoeff N k m T‖ := by ring
    _ ≤ 1 * ‖powCoeff N k m T‖ := by gcongr
    _ = ‖powCoeff N k m T‖ := one_mul _

/-- Coefficients divided by the uniform epsilon-growth majorant on the wide
support. -/
noncomputable def normalizedPoweredCoeffs
    (N k : ℕ) (σ T A δ : ℝ) (m : ℕ) : ℂ :=
  poweredLineCoeffs N k σ T m /
    ((A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ : ℝ) : ℂ)

/-- The powered coefficients, including any ordinate translation, satisfy the
unit coefficient condition required by the large-values theorem. -/
theorem norm_phaseShift_normalizedPoweredCoeffs_le_one
    (N k m : ℕ) (σ T c A δ : ℝ)
    (hN : 0 < N) (hσ : 0 ≤ σ)
    (hA : 0 < A) (hδ : 0 < δ)
    (hm : m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k))
    (hCoeff : ‖powCoeff N k m T‖ ≤ A * (m : ℝ) ^ δ) :
    ‖phaseShiftCoeffs c (normalizedPoweredCoeffs N k σ T A δ) m‖ ≤ 1 := by
  rw [norm_phaseShiftCoeffs]
  have hUpperNat : m ≤ 2 ^ k * N ^ k := (Finset.mem_Ioc.mp hm).2
  have hUpperNonneg : (0 : ℝ) ≤ (2 ^ k * N ^ k : ℕ) := Nat.cast_nonneg _
  have hmNonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hRpow : (m : ℝ) ^ δ ≤ ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ := by
    exact Real.rpow_le_rpow hmNonneg (by exact_mod_cast hUpperNat) hδ.le
  have hDenomPos : 0 < A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ := by
    have hUpperPos : 0 < 2 ^ k * N ^ k := mul_pos (pow_pos (by omega) k) (pow_pos hN k)
    have hUpperReal : (0 : ℝ) < (2 ^ k * N ^ k : ℕ) := by exact_mod_cast hUpperPos
    exact mul_pos hA (Real.rpow_pos_of_pos hUpperReal _)
  have hDenomNorm :
      ‖((A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ : ℝ) : ℂ)‖ =
        A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ := by
    simpa only [Complex.norm_real] using abs_of_pos hDenomPos
  rw [normalizedPoweredCoeffs, norm_div, hDenomNorm, div_le_one hDenomPos]
  exact (norm_poweredLineCoeffs_le N k m σ T hN hσ hm).trans
    (hCoeff.trans (mul_le_mul_of_nonneg_left hRpow hA.le))

/-- Exact normalized and translated powered-polynomial identity. -/
theorem wideDirichletPoly_normalizedPoweredCoeffs_translate
    (N k : ℕ) (σ T c u A δ : ℝ) (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k
        (phaseShiftCoeffs c (normalizedPoweredCoeffs N k σ T A δ)) u =
      ((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ) *
          powPoly N k (σ + I * (u + c)) T) /
        ((A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ : ℝ) : ℂ) := by
  rw [← wideDirichletPoly_poweredLineCoeffs_translate N k σ T c u hN hk]
  unfold wideDirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := by
    rw [Finset.mem_Ioc] at hm
    exact lt_of_le_of_lt (Nat.zero_le _) hm.1
  rw [phaseShiftCoeffs, phaseShiftCoeffs, if_neg hmPos.ne', if_neg hmPos.ne',
    normalizedPoweredCoeffs]
  ring

/-- Simultaneous block-and-ordinate pigeonholing. The chosen block is fixed on
the output subset, which is essential before invoking a large-values or
mean-value estimate. -/
theorem exists_dyadic_block_and_subset
    (Q k : ℕ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ)
    (hk : 0 < k)
    (hWide : ∀ t ∈ W, V ≤ ‖wideDirichletPoly Q k a t‖) :
    ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      ∀ t ∈ W', V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
  classical
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range k,
      V / k ≤ ‖dirichletPoly (2 ^ r * Q) a t‖ := by
    intro t ht
    exact exists_large_dyadic_block Q k a t V hk (hWide t ht)
  let index (t : ℝ) : ℕ :=
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hIndexMem : ∀ t ∈ W, index t ∈ Finset.range k := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hIndexLarge : ∀ t ∈ W,
      V / k ≤ ‖dirichletPoly (2 ^ index t * Q) a t‖ := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).2
  have hCard : W.card = ∑ r ∈ Finset.range k,
      (W.filter fun t => index t = r).card := by
    exact Finset.card_eq_sum_card_fiberwise hIndexMem
  have hCardReal : (W.card : ℝ) = ∑ r ∈ Finset.range k,
      ((W.filter fun t => index t = r).card : ℝ) := by
    exact_mod_cast hCard
  obtain ⟨r, hr, hrLarge⟩ := pigeonhole_real_sum k
    (fun r => ((W.filter fun t => index t = r).card : ℝ))
    (W.card : ℝ) (by rw [hCardReal]) hk
  refine ⟨r, hr, W.filter fun t => index t = r, Finset.filter_subset _ _, ?_, ?_⟩
  · have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    calc
      (W.card : ℝ) = k * ((W.card : ℝ) / k) := by field_simp
      _ ≤ k * ((W.filter fun t => index t = r).card : ℝ) := by gcongr
  · intro t ht
    rw [Finset.mem_filter] at ht
    simpa [ht.2] using hIndexLarge t ht.1

/-- A pointwise detector lower bound survives powering, left-endpoint scaling,
translation, and coefficient normalization with the exact displayed loss. -/
theorem normalized_powered_wide_lower
    (N k : ℕ) (σ T c u A δ L : ℝ)
    (hN : 0 < N) (hk : 0 < k) (hL : 0 ≤ L)
    (hDenom : 0 < A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ)
    (hDetector : L ≤ ‖detectPoly N (σ + I * (u + c)) T‖) :
    ((N ^ k : ℕ) : ℝ) ^ σ * L ^ k /
        (A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ) ≤
      ‖wideDirichletPoly (N ^ k) k
        (phaseShiftCoeffs c (normalizedPoweredCoeffs N k σ T A δ)) u‖ := by
  have hQNat : 0 < N ^ k := pow_pos hN k
  have hQ : (0 : ℝ) < (N ^ k : ℕ) := by exact_mod_cast hQNat
  have hQNorm : ‖((((N ^ k : ℕ) : ℝ) : ℂ) ^ (σ : ℂ))‖ =
      ((N ^ k : ℕ) : ℝ) ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
    rfl
  have hDenomNorm :
      ‖((A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ : ℝ) : ℂ)‖ =
        A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ δ := by
    simpa only [Complex.norm_real] using abs_of_pos hDenom
  have hPower : L ^ k ≤ ‖powPoly N k (σ + I * (u + c)) T‖ := by
    rw [powPoly, norm_pow]
    exact pow_le_pow_left₀ hL hDetector k
  rw [wideDirichletPoly_normalizedPoweredCoeffs_translate N k σ T c u A δ hN hk,
    norm_div, norm_mul, hQNorm, hDenomNorm]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower (Real.rpow_nonneg hQ.le σ)) hDenom.le

end RiemannZeta.GuthMaynard
