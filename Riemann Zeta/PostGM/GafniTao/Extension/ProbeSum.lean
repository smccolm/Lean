import GafniTao.FiniteEnergyColoring

#check Finset.sum_mul_sum
#check Finset.sum_mul
#check Finset.mul_sum
#check Finset.sum_comm
#check finProdFinEquiv
#check Finset.single_le_sum
#check Finset.eq_empty_iff_forall_not_mem

open scoped BigOperators

def qprod {A : Type} (S0 S1 S2 S3 : Finset A) :
    Finset ((A × A) × (A × A)) :=
  Finset.product (Finset.product S0 S1) (Finset.product S2 S3)

def qw {A : Type} (w : A -> Nat) (q : (A × A) × (A × A)) : Nat :=
  w q.1.1 * w q.1.2 * w q.2.1 * w q.2.2

example {A : Type} [DecidableEq A] (S0 S1 S2 S3 : Finset A)
    (w : A -> Nat) :
    (∑ q ∈ qprod S0 S1 S2 S3,
      qw w q) =
      (∑ x ∈ S0, w x) * (∑ x ∈ S1, w x) *
      (∑ x ∈ S2, w x) * (∑ x ∈ S3, w x) := by
  unfold qprod
  calc
    (∑ q ∈ (S0.product S1).product (S2.product S3), qw w q) =
        ∑ p ∈ S0.product S1, ∑ r ∈ S2.product S3, qw w (p, r) := by
      exact Finset.sum_product (S0.product S1) (S2.product S3)
        (fun q => qw w q)
    _ = _ := by
      dsimp only [qw]
