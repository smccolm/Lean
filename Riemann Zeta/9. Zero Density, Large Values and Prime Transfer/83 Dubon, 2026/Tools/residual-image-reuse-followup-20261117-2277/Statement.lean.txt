import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.ValuationSubring
import Deligne.Frobenius
import Deligne.GaloisReps

open scoped BigOperators

open Polynomial Nat AlgebraicClosure

variable {K L : Type _} [Field K] [Field L] {p : ℕ} [Fact (Nat.Prime p)] [Algebra K L]

/-- A Dirichlet character is defined as a monoid homomorphism which is periodic. -/
abbrev DirChar (R : Type _) [Monoid R] (n : ℕ) :=
  Units (ZMod n) →* Units R

instance : NoZeroSMulDivisors K (AlgebraicClosure K) := by
  exact Module.Free.noZeroSMulDivisors K (AlgebraicClosure K)

/-- The map from the algebraic closure for K to L when L is algebraically closed -/
noncomputable def functioriality (h : IsAlgClosed L) : AlgebraicClosure K →+* L :=
  AlgHom.toRingHom (IsAlgClosed.lift (isAlgebraic K))

/-- An arbitrary fixed map from the algebraic closure of ℚ into ℂ -/
noncomputable def algClosRatToComplex : AlgebraicClosure ℚ →+* ℂ :=
  functioriality Complex.isAlgClosed

/-- An arbitrary fixed map from algebraic closure of ℚ into alg closure of ℚ_p. -/
noncomputable def algClosRatToPAdic (p : ℕ) [Fact (Nat.Prime p)] :
    AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[p] := 
    functioriality (isAlgClosed ℚ_[p])

def ZMod.Unit.mk {N : ℕ} {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ N) : (ZMod N)ˣ
    where
  val := q
  inv := q⁻¹
  val_inv := by
    have : Coprime q N := (Nat.Prime.coprime_iff_not_dvd h).mpr hqN
    apply ZMod.coe_mul_inv_eq_one q
    exact this
  inv_val := by
    rw [mul_comm, ZMod.coe_mul_inv_eq_one q]
    have : Coprime q N := (Nat.Prime.coprime_iff_not_dvd h).mpr hqN
    exact this

/-- The Hecke operator -/
noncomputable def heckeOperator {N : ℕ} {k : ℕ} {q : ℕ} (f : ModularForm (Gamma1 N) k)
    (h : Nat.Prime q) (χ : DirChar ℂ N) (hqN : ¬q ∣ N) (z : UpperHalfPlane) : ℂ :=
  ∑ n in Finset.range q,
      f
        ⟨(z + n) / q, by
          have : 0 < q := by apply Nat.Prime.pos h
          have hz : 0 < z.im := UpperHalfPlane.im_pos z
          ring_nf
          simp only [Complex.add_im, Complex.mul_im, Complex.inv_re, Complex.nat_cast_re,
            UpperHalfPlane.coe_im, Complex.inv_im, Complex.nat_cast_im, neg_zero, zero_div,
            MulZeroClass.zero_mul, add_zero, MulZeroClass.mul_zero]
          simp at *
          refine' mul_pos hz _
          have hnpos : 0 < Complex.normSq q :=
            by
            simp only [Complex.normSq_pos, Ne.def, Nat.cast_eq_zero]
            linarith
          ring_nf
          refine' mul_pos (Iff.mpr Nat.cast_pos this) (Iff.mpr inv_pos hnpos)⟩ +
      χ (ZMod.Unit.mk h hqN) * q ^ (k - 1) * f
        ⟨q * z, by
          have : 0 < q := by apply Nat.Prime.pos h
          have hz : 0 < z.im := UpperHalfPlane.im_pos z
          ring_nf
          simp at *
          refine mul_pos ?ha hz
          norm_cast⟩

/-- Only asking that it is an eigenvector for the good primes. -/
def IsWeakEigenform {N : ℕ} {k : ℕ} (f : ModularForm (Gamma1 N) k) (χ : DirChar ℂ N) :
    Prop :=
  f ≠ 0 ∧
    ∀ {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ N),
      ∃ a : ℂ, ∀ z : UpperHalfPlane, heckeOperator f h χ hqN z = a * f z

/-- An eigenvalue of the Hecke operator. -/
noncomputable def eigenvalue {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} (hqN : ¬q ∣ N) {χ : DirChar ℂ N}
    (hf : IsWeakEigenform f χ) : ℂ :=
  Exists.choose (hf.2 h hqN)

/--The eigenvalues of the Hecke operator are algebraic. -/
theorem EigenvaluesAlgebraic {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} (hqN : ¬q ∣ N) {χ : DirChar ℂ N}
    (hf : IsWeakEigenform f χ) :
    ∃ a : AlgebraicClosure ℚ, algClosRatToComplex a = eigenvalue h hqN hf := sorry

/-- The algebraic eigenvalue of the Hecke operator -/
noncomputable def AlgEigenvalue {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} {χ : DirChar ℂ N} (hf : IsWeakEigenform f χ)
    (hqN : ¬q ∣ N) : AlgebraicClosure ℚ :=
  Exists.choose (EigenvaluesAlgebraic h hqN hf)

theorem NonnunitPrimesInComap (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤) :
    ∃ q : ℕ, Nat.Prime q ∧ ↑q ∈ LocalRing.maximalIdeal (v.comap (algebraMap ℚ (AlgebraicClosure ℚ))) :=
  sorry

noncomputable def q (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤) : ℕ :=
  Exists.choose (NonnunitPrimesInComap v h)

theorem q.isPrime {v : ValuationSubring (AlgebraicClosure ℚ)} (h : v ≠ ⊤) :
    Nat.Prime (q v h) := sorry

def ZMod.Unit {N : ℕ} {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ p * N) : (ZMod N)ˣ
    where
  val := q
  inv := q⁻¹
  val_inv := by
    have : Coprime q (p * N) := (Nat.Prime.coprime_iff_not_dvd h).mpr hqN
    apply ZMod.coe_mul_inv_eq_one q
    have hqN : Coprime q N := Coprime.coprime_mul_left_right this
    exact hqN
  inv_val := by
    rw [mul_comm, ZMod.coe_mul_inv_eq_one q]
    have : Coprime q (p * N) := (Nat.Prime.coprime_iff_not_dvd h).mpr hqN
    have hqN : Coprime q N := Coprime.coprime_mul_left_right this
    exact hqN

theorem div (N : ℕ) (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤)
    (hqpN : ¬q v h ∣ p * N) : ¬q v h ∣ N :=
  by
  have hco : Coprime (q v h) (p * N) :=
    by
    rw [Nat.Prime.coprime_iff_not_dvd]
    exact hqpN
    exact q.isPrime h
  have : Coprime (q v h) N := Coprime.coprime_mul_left_right hco
  rw [Nat.Prime.coprime_iff_not_dvd] at *
  exact this
  exact q.isPrime h
  exact q.isPrime h

section

variable (R : Type _) [CommRing R] [TopologicalSpace R] [TopologicalRing R] [NumberField K]
  [Algebra K L] [IsGalois K L]

open ValuationSubring

variable {R}

instance : NormedField (AlgebraicClosure ℚ_[p]) := sorry

/-- Units (ZMod n) →* Units ℂ -/
noncomputable def DirCharComplex {N : ℕ} (χ : DirChar (AlgebraicClosure ℚ) N) :
    DirChar ℂ N :=
  (Units.map algClosRatToComplex.toMonoidHom).comp χ

/-- Units (ZMod n) →* Units ℚ_[p] -/
noncomputable def DirCharAlgClosRat {N : ℕ} {p : ℕ} [Fact (Nat.Prime p)]
    (χ : DirChar (AlgebraicClosure ℚ) N) :
    DirChar (AlgebraicClosure ℚ_[p]) N :=
  (Units.map (algClosRatToPAdic p).toMonoidHom).comp χ

/-- Deligne's theorem -/
-- If f is a weight k modular eigenform of level N and character χ, and if p is a prime
theorem Deligne {N : ℕ} {k : ℕ} {f : ModularForm (Gamma1 N) k} (χ : DirChar (AlgebraicClosure ℚ) N) (hf : IsWeakEigenform f (DirCharComplex χ)) :
-- then there is an associated 2-dimensional Galois representation ρ
    ∃ (ρ : GaloisRep (AlgebraicClosure ℚ_[p])),
-- unramified outside Np such that if q not dividing Np, q is a prime
      ∀ (v : ValuationSubring (AlgebraicClosure ℚ)) (hv : v ≠ ⊤) (hqpN : ¬ q v hv ∣ p * N), (IsUnramified ρ v)
-- Let `a` be the algebraic eigenvalue of the Hecke operator corresponding to q and takes values in `AlgebraicClosure ℚ_[p]`
    ∧ let a := C ((algClosRatToPAdic p) (AlgEigenvalue (q.isPrime hv) hf (div N v hv hqpN)))
-- and let `χq` be the Dirichlet character χ that also takes values in `AlgebraicClosure ℚ_[p]`.
    let χq  := (Units.coeHom (AlgebraicClosure ℚ_[p])).comp (DirCharAlgClosRat χ) (ZMod.Unit (q.isPrime hv) hqpN)
-- Then the characteristic polynomial of ρ(Frob) is  X^2 - aX + q^{k-1} χ(q).
Matrix.charpoly (Matrix.of (ρ.toMonoidHom (Frob ℚ (AlgebraicClosure ℚ) v hv))) =
X ^ 2 - (a * X) + ((q v hv) ^ (k - 1) : (AlgebraicClosure ℚ_[p])[X]) * (C χq) := sorry

end
