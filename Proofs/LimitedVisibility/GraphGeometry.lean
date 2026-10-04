import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-! Geometry is independent of the random-walk probability law. -/
namespace LimitedVisibility

variable {V : Type*} (G : SimpleGraph V)

/-- Vertices at which the random phase is still running. -/
abbrev Outside (t : V) (r : ℕ) := {v : V // r < G.dist v t}

theorem adjacent_dist_le (hG : G.Connected) {u v t : V} (h : G.Adj u v) :
    G.dist v t ≤ G.dist u t + 1 := by
  have ht := hG.dist_triangle (u := v) (v := u) (w := t)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at ht
  omega

theorem adjacent_dist_bounds (hG : G.Connected) {u v t : V} (h : G.Adj u v) :
    G.dist v t ≤ G.dist u t + 1 ∧ G.dist u t ≤ G.dist v t + 1 :=
  ⟨adjacent_dist_le G hG h, adjacent_dist_le G hG h.symm⟩

/-- A single edge cannot jump from outside the ball to its strict interior. -/
theorem entry_on_sphere (hG : G.Connected) {u v t : V} {r : ℕ}
    (h : G.Adj u v) (hu : r < G.dist u t) (hv : G.dist v t ≤ r) :
    G.dist v t = r := by
  have := adjacent_dist_le G hG h.symm (t := t)
  omega

/-- A finite first-hit certificate; no infinite-path probability space is needed. -/
structure FirstHit (t : V) (r : ℕ) (x : ℕ → V) (T : ℕ) : Prop where
  steps : ∀ n, n < T → G.Adj (x n) (x (n + 1))
  before : ∀ n, n < T → r < G.dist (x n) t
  hit : G.dist (x T) t ≤ r

theorem firstHit_on_sphere (hG : G.Connected) {t : V} {r T : ℕ} {x : ℕ → V}
    (hx : FirstHit G t r x T) (hout : r < G.dist (x 0) t) :
    G.dist (x T) t = r := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    have hh := hx.hit
    rw [hz] at hh
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  exact entry_on_sphere G hG (hx.steps n (by omega)) (hx.before n (by omega)) hx.hit

/-- Random steps followed by a shortest deterministic suffix. -/
noncomputable def routeLength (t : V) (x : ℕ → V) (T : ℕ) : ℕ := T + G.dist (x T) t

theorem routeLength_eq_add_radius (hG : G.Connected) {t : V} {r T : ℕ} {x : ℕ → V}
    (hx : FirstHit G t r x T) (hout : r < G.dist (x 0) t) :
    routeLength G t x T = T + r := by
  rw [routeLength, firstHit_on_sphere G hG hx hout]

theorem visible_firstHit {t : V} {r T : ℕ} {x : ℕ → V}
    (hx : FirstHit G t r x T) (hin : G.dist (x 0) t ≤ r) :
    T = 0 ∧ routeLength G t x T = G.dist (x 0) t := by
  have hz : T = 0 := by
    by_contra hn
    exact (not_lt_of_ge hin) (hx.before 0 (Nat.pos_of_ne_zero hn))
  simp [hz, routeLength]

theorem shortest_suffix (hG : G.Connected) (v t : V) :
    ∃ p : G.Walk v t, p.IsPath ∧ p.length = G.dist v t := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v t
  exact ⟨p, p.isPath_of_length_eq_dist hp, hp⟩

end LimitedVisibility
