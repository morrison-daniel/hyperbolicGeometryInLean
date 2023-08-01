import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators ComplexConjugate

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

namespace Sign

def pos : Sign := ⟨  1, by left; rfl ⟩
def neg : Sign := ⟨ -1, by right; rfl ⟩

end Sign
