import Hyperbolic.PseudoInnerProductSpace
import Mathlib.Algebra.BigOperators.Basic

open BigOperators ComplexConjugate IsROrC

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

namespace Sign

def pos : Sign := ⟨  1, by left; rfl ⟩
def neg : Sign := ⟨ -1, by right; rfl ⟩

end Sign

structure PseudoEuclideanSpace (𝕜 : Type _) (ι : Type _) [IsROrC 𝕜] [Fintype ι] [DecidableEq ι] where
  signature : ι → Sign
  inner := fun (v w : ι → 𝕜) => ∑ i, conj (v i) * (w i) * ofReal (signature (i))

attribute [class] PseudoEuclideanSpace

variable {𝕜 : Type _} [IsROrC 𝕜]
variable {ι : Type _} [Fintype ι] [DecidableEq ι]
variable {E : PseudoEuclideanSpace 𝕜 ι}

instance : PseudoInnerProductSpace 𝕜 (ι → 𝕜) where
  inner := E.inner
  conj_symm := sorry
  add_left := sorry
  smul_left := sorry
  nondeg := sorry



