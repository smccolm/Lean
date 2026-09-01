import GafniTao.FordS4Resolution
import GafniTao.FordEquation34SourceS3
import GafniTao.FordLemma32Arithmetic

/-!
# Ford equation (3.7): source `S₃(p)` consumer

This module composes the literal source `S₃(p)` entry, the resolved `S₄`
alternative, and the exact `S₆`-to-`L` injection.  The output retains the
translated polynomial system used by the proof.
-/

namespace GafniTao

noncomputable section

theorem ford_equation_3_7_source
    {k d T P p s Q q r M : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hk2 : 2 ≤ k) (hdk : d ≤ k) (hds : d + 1 ≤ s)
    (hq : 0 < q) (hp : Nat.Prime p) (hkp : k < p)
    (hr : 0 < r) (hdr : d < r) (hrk : r ≤ k) (hpT : ¬p ∣ T)
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M < Q) :
    ∃ c : ZMod p,
      fordS3Count (P := P) (p := p) Ψ hdk s Q q ≤
        2 * k.factorial *
          p ^ ((2 * s - d) +
            ((r - d - 1) * (r - d) / 2 + r * d)) *
          fordLCount
            (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
            s P (Q / p) p q r := by
  have hs : 1 ≤ s := by omega
  have hds' : d ≤ s := by omega
  have hdp : d < p := lt_of_le_of_lt hdk hkp
  obtain ⟨c, hcReal⟩ := ford_equation_3_4_source
    (P := P) (p := p) (s := s) (Q := Q) (q := q)
    Ψ hdk (by omega) hds' hq hp hdp
  refine ⟨c, ?_⟩
  have hc : fordS3Count (P := P) (p := p) Ψ hdk s Q q ≤
      d.factorial * p ^ (2 * s - d) *
        fordS4Count (P := P) Ψ hdk s Q q c := by
    exact_mod_cast hcReal
  have hS4 := fordS4Count_le_two_S6
    (P := P) (p := p) (q := q) (r := r) Ψ hdk c hs hr hpM hQ
  have hS6 := ford_S6_le_L Ψ (fordS4TranslationScale q c)
    (s := s) (P := P) (Q := Q / p) (p := p) (q := q) (r := r)
    hp hr hk2 hkp hdk hdr hrk hpT
  let E : ℕ := (r - d - 1) * (r - d) / 2 + r * d
  let L : ℕ := fordLCount
    (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
    s P (Q / p) p q r
  have hfactorial : d.factorial * (k - d).factorial ≤ k.factorial :=
    ford_factorial_mul_factorial_sub_le_factorial hdk
  calc
    fordS3Count (P := P) (p := p) Ψ hdk s Q q ≤
        d.factorial * p ^ (2 * s - d) *
          fordS4Count (P := P) Ψ hdk s Q q c := hc
    _ ≤ d.factorial * p ^ (2 * s - d) *
        (2 * fordS6Count Ψ (fordS4TranslationScale q c)
          s P (Q / p) p q r hdk) :=
      Nat.mul_le_mul_left _ hS4
    _ ≤ d.factorial * p ^ (2 * s - d) *
        (2 * (((k - d).factorial * p ^ E) * L)) := by
      dsimp [E, L]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hS6)
    _ = 2 * (d.factorial * (k - d).factorial) *
        p ^ ((2 * s - d) + E) * L := by
      rw [pow_add]
      ring
    _ ≤ 2 * k.factorial * p ^ ((2 * s - d) + E) * L := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hfactorial))

#print axioms ford_equation_3_7_source

end

end GafniTao
