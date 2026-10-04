import LimitedVisibility.FundamentalMatrix
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! A positive Dirichlet inverse bounds all partial sums of a nonnegative
forced recurrence. This single lemma will supply the first three moments. -/
namespace LimitedVisibility
open Matrix
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- If `(I-Q)` preserves comparison in the reverse direction, summable input
in `a(n+1) = b(n) + Q a(n)` gives summable nonnegative output. -/
theorem summable_recurrence {Q : Matrix U U ℝ} (hN : IsUnit (1 - Q).det)
    (comparison : ∀ x, 0 ≤ (1 - Q) *ᵥ x → 0 ≤ x)
    (a b : ℕ → U → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hbSum : ∀ i, Summable (fun n => b n i))
    (h0 : a 0 = 0) (hstep : ∀ n, a (n + 1) = b n + Q *ᵥ a n) :
    ∀ i, Summable (fun n => a n i) := by
  let B : U → ℝ := fun i => ∑' n, b n i
  let c := (1 - Q)⁻¹ *ᵥ B
  have hc : (1 - Q) *ᵥ c = B := by
    simp only [c, mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, one_mulVec]
  have telescope (n : ℕ) :
      (1 - Q) *ᵥ (∑ k ∈ Finset.range n, a k) = (∑ k ∈ Finset.range n, b k) - a n := by
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, mulVec_add, ih, sub_mulVec, one_mulVec,
        Finset.sum_range_succ, hstep]
      abel
  intro i
  apply summable_of_sum_range_le (fun n => ha n i) (c := c i)
  intro n
  have hbound : 0 ≤ (1 - Q) *ᵥ (c - ∑ k ∈ Finset.range n, a k) := by
    rw [mulVec_sub, hc, telescope]
    intro j
    have hj := (hbSum j).sum_le_tsum (Finset.range n) (fun k _ => hb k j)
    simp only [Pi.sub_apply, Finset.sum_apply, B] at *
    have := ha n j
    linarith
  have := comparison _ hbound i
  simpa only [Pi.sub_apply, Pi.zero_apply, Finset.sum_apply, sub_nonneg] using this

end LimitedVisibility
