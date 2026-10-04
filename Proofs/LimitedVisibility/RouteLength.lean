import LimitedVisibility.Absorption
import LimitedVisibility.Variance

namespace LimitedVisibility
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (hG : G.Connected) (t : V) (r : ℕ)

omit [DecidableEq V] in
include hG in
theorem graph_hitting_nonneg : ∀ n i, 0 ≤ hittingMass (transition G t r) n i := by
  classical
  exact hittingMass_nonneg (transition_nonneg G t r) (transition_substochastic G hG t r)

/-- The probability space carries the random-phase duration; it is degenerate
at zero if the source is already visible. -/
noncomputable def routeBaseLaw (s : V) : DiscreteLaw := by
  classical
  exact if hs : r < G.dist s t then hittingLaw (graph_regular G hG t r) (graph_hitting_nonneg G hG t r) ⟨s, hs⟩
    else DiscreteLaw.point

/-- The geometric theorems justify this observable: T+r outside, distance inside. -/
noncomputable def routeObservable (s : V) (n : ℕ) : ℝ :=
  if r < G.dist s t then (n : ℝ) + (r : ℝ) else (G.dist s t : ℝ)

noncomputable def expectedRoute (s : V) : ℝ :=
  ∫ n, routeObservable G t r s n ∂(routeBaseLaw G hG t r s).toPMF.toMeasure

noncomputable def routeVariance (s : V) : ℝ :=
  ProbabilityTheory.variance (routeObservable G t r s) (routeBaseLaw G hG t r s).toPMF.toMeasure

/-- The actual PMF on natural-number route lengths. -/
noncomputable def routePMF (s : V) : PMF ℕ := by
  classical
  exact (routeBaseLaw G hG t r s).toPMF.map
    (fun n => if r < G.dist s t then n + r else G.dist s t)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
include hG in
theorem routeObservable_eq_length {s : V} {x : ℕ → V} {T : ℕ}
    (hx : FirstHit G t r x T) (hs : x 0 = s) :
    routeObservable G t r s T = (routeLength G t x T : ℝ) := by
  classical
  by_cases hout : r < G.dist s t
  · have ho : r < G.dist (x 0) t := by rwa [hs]
    rw [routeObservable, if_pos hout, routeLength_eq_add_radius G hG hx ho, Nat.cast_add]
  · have hin : G.dist (x 0) t ≤ r := by rw [hs]; omega
    rw [routeObservable, if_neg hout, (visible_firstHit G hx hin).2, hs]

/- The visible case needs no absorption or moment hypothesis. -/
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem visible_observable_statistics {s : V} (hs : G.dist s t ≤ r) :
    (∫ n, routeObservable G t r s n ∂DiscreteLaw.point.toPMF.toMeasure) = (G.dist s t : ℝ) ∧
    ProbabilityTheory.variance (routeObservable G t r s) DiscreteLaw.point.toPMF.toMeasure = 0 := by
  have he : routeObservable G t r s = fun _ => (G.dist s t : ℝ) := by
    funext n; simp [routeObservable, not_lt.mpr hs]
  rw [he]
  exact DiscreteLaw.point.deterministic_statistics _

theorem visible_route_statistics {s : V}
    (hs : G.dist s t ≤ r) :
    expectedRoute G hG t r s = (G.dist s t : ℝ) ∧ routeVariance G hG t r s = 0 := by
  classical
  have hn : ¬ r < G.dist s t := not_lt.mpr hs
  have he : routeObservable G t r s = fun _ => (G.dist s t : ℝ) := by
    funext n; simp [routeObservable, hn]
  simpa [expectedRoute, routeVariance, DiscreteLaw.expect, DiscreteLaw.variance, he] using
    (routeBaseLaw G hG t r s).deterministic_statistics (G.dist s t : ℝ)

theorem outside_route_statistics
    (hN : IsUnit (1 - transition G t r).det)
    (s : Outside G t r) :
    expectedRoute G hG t r s.val = (r : ℝ) + meanVector (1 - transition G t r)⁻¹ s ∧
    routeVariance G hG t r s.val = secondVector (1 - transition G t r)⁻¹ s - (meanVector (1 - transition G t r)⁻¹ s) ^ 2 := by
  classical
  have he : routeObservable G t r s.val = fun n : ℕ => (n : ℝ) + (r : ℝ) := by
    funext n; simp [routeObservable, s.property]
  simpa [expectedRoute, routeVariance, DiscreteLaw.expect, DiscreteLaw.variance, he, routeBaseLaw, s.property] using
    shifted_hitting_statistics hN (graph_regular G hG t r) (graph_hitting_nonneg G hG t r) s (r : ℝ)

end LimitedVisibility
