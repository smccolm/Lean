import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

example {X : ℝ} {a : ℕ} (hX : 0 < X) (ha : 0 < a) :
    (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) =
      X ^ (-(1 / 4 : ℝ)) * (a : ℝ) ^ (1 / 4 : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  rw [Real.div_rpow hX.le haR.le, Real.rpow_neg haR.le]
  field_simp

example {a b q : ℕ} [NeZero q] {X Q η R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hQ : 0 < Q) :
    let W := Real.sqrt (Nat.gcd (0 : ℕ) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceXTransition a X Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (a : ℝ) * (((a : ℝ) * b)⁻¹)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd (0 : ℕ) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  change W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceXTransition a X Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (a : ℝ) * (((a : ℝ) * b)⁻¹))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hSource :
      dfiEquation29SourceXTransition a X Q η ^ (3 / 4 + η) =
        (a : ℝ) ^ (3 / 4 + η) * X ^ (3 / 4 + η) *
          Q ^ ((-2 + η) * (3 / 4 + η)) :=
    dfiEquation29SourceXTransition_rpow a hX hQ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by unfold dfiEquation29SourceXTransition; positivity :
        0 ≤ dfiEquation29SourceXTransition a X Q η),
    hSource]
  have hXa :
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) =
        X ^ (-(1 / 4 : ℝ)) * (a : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hX.le haR.le, Real.rpow_neg haR.le]
    field_simp
  rw [hXa]
  have hXpow : X ^ (-(1 / 4 : ℝ)) * X ^ (3 / 4 + η) =
      X ^ (1 / 2 + η) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hapow : (a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ (3 / 4 + η) =
      (a : ℝ) * (a : ℝ) ^ η := by
    calc
      _ = (a : ℝ) ^ ((1 / 4 : ℝ) + (3 / 4 + η)) :=
        (Real.rpow_add haR _ _).symm
      _ = (a : ℝ) ^ (1 + η) := by congr 1 <;> ring
      _ = (a : ℝ) ^ (1 : ℝ) * (a : ℝ) ^ η :=
        Real.rpow_add haR 1 η
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = 2 ^ (3 / 4 + η) *
        (X ^ (-(1 / 4 : ℝ)) * X ^ (3 / 4 + η)) *
        ((a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ (3 / 4 + η)) *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (((a : ℝ) * b)⁻¹)) := by ring
    _ = _ := by
      rw [hXpow, hapow]
      ring

end RiemannZeta.GuthMaynard
