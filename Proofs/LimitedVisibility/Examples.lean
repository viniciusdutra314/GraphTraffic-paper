import LimitedVisibility.Main

namespace LimitedVisibility
open Matrix

/-- Two vertices joined by an edge, radius zero: the transient matrix vanishes. -/
theorem twoVertex_transition : transition (⊤ : SimpleGraph Bool) false 0 = 0 := by
  classical
  ext i j
  have hi : i.val = true := by
    have h := i.property
    cases hv : i.val <;> simp_all [SimpleGraph.dist_self]
  have hj : j.val = true := by
    have h := j.property
    cases hv : j.val <;> simp_all [SimpleGraph.dist_self]
  simp [transition, step, hi, hj]

/-- The walk across a single edge has length one and variance zero. -/
theorem twoVertex_route :
    expectedRoute (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 0 true = 1 ∧
    routeVariance (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 0 true = 0 := by
  classical
  have h := route_statistics (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 0
    true
  norm_num [SimpleGraph.dist_top_of_ne, twoVertex_transition, meanVector, secondVector, ones,
    Matrix.sub_mulVec, Matrix.smul_mulVec_assoc] at h
  exact h

/-- If every vertex is visible, the transient type is empty. -/
example :
    expectedRoute (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 1 true = 1 ∧
    routeVariance (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 1 true = 0 := by
  simpa [SimpleGraph.dist_top_of_ne] using
    visible_route_statistics (⊤ : SimpleGraph Bool) SimpleGraph.top_connected false 1
      (s := true) (by simp [SimpleGraph.dist_top_of_ne])

end LimitedVisibility
