import LimitedVisibility.RouteLength

namespace LimitedVisibility
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Final result with the genuine matrix inverse and mathlib expectation/variance.
Finiteness and connectivity imply absorption, finite moments and nonsingularity. -/
theorem route_statistics (hG : G.Connected) (t : V) (r : ℕ)
    (s : V) :
    let N := (1 - transition G t r)⁻¹
    (expectedRoute G hG t r s =
      if hs : r < G.dist s t then (r : ℝ) + meanVector N ⟨s, hs⟩ else (G.dist s t : ℝ)) ∧
    (routeVariance G hG t r s =
      if hs : r < G.dist s t then secondVector N ⟨s, hs⟩ - (meanVector N ⟨s, hs⟩) ^ 2 else 0) := by
  classical
  have hdet := transition_det_isUnit G hG t r
  dsimp only
  by_cases hs : r < G.dist s t
  · simp only [dif_pos hs]
    exact outside_route_statistics G hG t r hdet ⟨s, hs⟩
  · simp only [dif_neg hs]
    exact visible_route_statistics G hG t r (Nat.le_of_not_gt hs)

end LimitedVisibility
