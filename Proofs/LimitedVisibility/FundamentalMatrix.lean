import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace LimitedVisibility
open Matrix

variable {U : Type*} [Fintype U] [DecidableEq U]

def ones : U → ℝ := fun _ => 1

def meanVector (N : Matrix U U ℝ) : U → ℝ := N *ᵥ ones

def secondVector (N : Matrix U U ℝ) : U → ℝ :=
  ((2 : ℝ) • N - 1) *ᵥ (N *ᵥ ones)

end LimitedVisibility
