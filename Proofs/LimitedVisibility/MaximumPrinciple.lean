import LimitedVisibility.TransitionMatrix
import LimitedVisibility.FundamentalMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! A function which is superharmonic wherever it is negative cannot have a
negative minimum on a finite connected graph if it vanishes at the target. -/
namespace LimitedVisibility
open Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Apply mathlib's Laplacian positivity and kernel characterization to the
negative part of `f`. Zero energy makes it constant on a connected graph. -/
theorem minimum_principle (hG : G.Connected) (t : V) (f : V → ℝ) (ht : f t = 0)
    (hsuper : ∀ v, f v < 0 → ∑ w ∈ G.neighborFinset v, f w ≤ (G.degree v : ℝ) * f v) :
    ∀ v, 0 ≤ f v := by
  classical
  let g : V → ℝ := fun v => min (f v) 0
  have henergy : g ⬝ᵥ (G.lapMatrix ℝ *ᵥ g) ≤ 0 := by
    apply Finset.sum_nonpos
    intro v _
    rw [G.lapMatrix_mulVec_apply]
    by_cases hv : f v < 0
    · have hsum := (Finset.sum_le_sum (fun w (_ : w ∈ G.neighborFinset v) =>
        min_le_left (f w) 0)).trans (hsuper v hv)
      exact mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _)
        (sub_nonneg.mpr (by simpa only [g, min_eq_left hv.le] using hsum))
    · simp [g, min_eq_right (le_of_not_gt hv)]
  have hzero : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) g g = 0 := by
    rw [Matrix.toLinearMap₂'_apply']
    exact le_antisymm henergy (by simpa using (G.posSemidef_lapMatrix ℝ).2 g)
  have hconstant := (G.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable g).mp hzero
  intro v
  have := hconstant v t (hG v t)
  simpa [g, ht, min_eq_right_iff] using this

/-- Extend a transient vector by zero on the visible ball. -/
noncomputable def extendByZero (t : V) (r : ℕ) (x : Outside G t r → ℝ) (v : V) : ℝ :=
  if h : r < G.dist v t then x ⟨v, h⟩ else 0

/-- Dirichlet comparison: (I-Q)x ≥ 0 implies x ≥ 0. -/
theorem transition_comparison (hG : G.Connected) (t : V) (r : ℕ)
    (x : Outside G t r → ℝ) (hx : 0 ≤ (1 - transition G t r) *ᵥ x) : 0 ≤ x := by
  classical
  let f := extendByZero G t r x
  have hf : ∀ v, 0 ≤ f v := by
    apply minimum_principle G hG t f
    · simp [f, extendByZero, SimpleGraph.dist_self]
    intro v hv
    have hout : r < G.dist v t := by
      by_contra hn
      simp [f, extendByZero, hn] at hv
    have hxv := hx ⟨v, hout⟩
    have he : (transition G t r *ᵥ x) ⟨v, hout⟩ =
        (G.degree v : ℝ)⁻¹ * ∑ w ∈ G.neighborFinset v, f w := by
      have hext : (transition G t r *ᵥ x) ⟨v, hout⟩ = ∑ w, step G v w * f w := by
        symm
        apply Finset.sum_congr_set {w : V | r < G.dist w t}
        · intro w hw; change r < G.dist w t at hw
          simp [transition, f, extendByZero, hw]
        · intro w hw; change ¬ r < G.dist w t at hw
          simp [f, extendByZero, hw]
      rw [hext]
      simp only [step, ite_mul, zero_mul, ← Finset.sum_filter, Finset.mul_sum]
      rw [G.neighborFinset_eq_filter]
    rw [sub_mulVec, one_mulVec] at hxv
    change 0 ≤ x ⟨v, hout⟩ - (transition G t r *ᵥ x) ⟨v, hout⟩ at hxv
    rw [he] at hxv
    have hd : 0 < (G.degree v : ℝ) := by
      exact_mod_cast outside_degree_pos G hG (⟨v, hout⟩ : Outside G t r)
    have hfv : f v = x ⟨v, hout⟩ := by simp [f, extendByZero, hout]
    rw [← hfv] at hxv
    have := (mul_le_mul_iff_of_pos_left hd).mpr (sub_nonneg.mp hxv)
    simpa [← mul_assoc, ne_of_gt hd] using this
  intro i
  simpa [f, extendByZero, i.property] using hf i.val

theorem transition_det_isUnit (hG : G.Connected) (t : V) (r : ℕ) :
    IsUnit (1 - transition G t r).det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (injective_iff_map_eq_zero (1 - transition G t r).mulVecLin).mpr
  intro x hx
  change (1 - transition G t r) *ᵥ x = 0 at hx
  exact le_antisymm
    (neg_nonneg.mp (transition_comparison G hG t r (-x) (by rw [mulVec_neg, hx, neg_zero])))
    (transition_comparison G hG t r x (by rw [hx]))

end LimitedVisibility
