import LimitedVisibility.GraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Mul

namespace LimitedVisibility
open scoped BigOperators

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance outsideFintype (t : V) (r : ℕ) : Fintype (Outside G t r) := by
  classical
  unfold Outside
  infer_instance

/-- Uniform choice among all neighbors, including visible ones. -/
noncomputable def step (i j : V) : ℝ := if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0

/-- The restriction of the full transition probabilities to transient vertices. -/
noncomputable def transition (t : V) (r : ℕ) : Matrix (Outside G t r) (Outside G t r) ℝ :=
  fun i j => step G i.val j.val

theorem outside_degree_pos (hG : G.Connected) {t : V} {r : ℕ} (i : Outside G t r) :
    0 < G.degree i.val := by
  apply (G.degree_pos_iff_exists_adj _).mpr
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i.val t
  have hpos : 0 < p.length := by rw [hp]; have := i.property; omega
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (show 0 < p.length from hpos)⟩

theorem step_nonneg (i j : V) : 0 ≤ step G i j := by
  unfold step
  split_ifs <;> positivity

theorem step_sum {i : V} (hi : 0 < G.degree i) : ∑ j, step G i j = 1 := by
  classical
  simp only [step, ← Finset.sum_filter]
  rw [← G.neighborFinset_eq_filter]
  simp [ne_of_gt hi]

theorem transition_nonneg (t : V) (r : ℕ) (i j : Outside G t r) :
    0 ≤ transition G t r i j := step_nonneg G _ _

theorem transition_substochastic (hG : G.Connected) (t : V) (r : ℕ)
    (i : Outside G t r) : ∑ j, transition G t r i j ≤ 1 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun v : V => r < G.dist v t) (fun j => step G i.val j)
  have hnonneg : 0 ≤ ∑ j : {v : V // ¬ r < G.dist v t}, step G i.val j.val :=
    Finset.sum_nonneg (fun j _ => step_nonneg G _ _)
  have hsum := step_sum G (outside_degree_pos G hG i)
  change (∑ j : {v : V // r < G.dist v t}, step G i.val j.val) ≤ 1
  linarith

/-- Exactly the probability omitted by a transient row. -/
noncomputable def exitProb (t : V) (r : ℕ) (i : Outside G t r) : ℝ :=
  1 - ∑ j, transition G t r i j

theorem exitProb_nonneg (hG : G.Connected) (t : V) (r : ℕ) (i : Outside G t r) :
    0 ≤ exitProb G t r i := sub_nonneg.mpr (transition_substochastic G hG t r i)

theorem exitProb_eq_visible_sum (hG : G.Connected) (t : V) (r : ℕ)
    (i : Outside G t r) :
    exitProb G t r i = ∑ j : {v : V // G.dist v t ≤ r}, step G i.val j.val := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun v : V => G.dist v t ≤ r) (fun j => step G i.val j)
  rw [step_sum G (outside_degree_pos G hG i)] at hsplit
  have he := (Equiv.subtypeEquivRight (fun v : V => not_le (a := G.dist v t) (b := r))).sum_comp
    (fun j : Outside G t r => step G i.val j.val)
  change (∑ j : {v : V // ¬ G.dist v t ≤ r}, step G i.val j.val) =
    ∑ j : Outside G t r, step G i.val j.val at he
  rw [he] at hsplit
  exact (eq_sub_iff_add_eq.mpr hsplit).symm

end LimitedVisibility
