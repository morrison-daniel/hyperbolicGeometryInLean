import Hyperbolic.PseudoInnerProductSpace

open BigOperators ComplexConjugate IsROrC PseudoInnerProductSpace

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

namespace Sign

def pos : Sign := ⟨  1, by left; rfl ⟩
def neg : Sign := ⟨ -1, by right; rfl ⟩

end Sign

@[reducible]
structure PseudoEuclideanSpace (𝕜 : Type _) (ι : Type _) [IsROrC 𝕜] [Fintype ι] [DecidableEq ι] where
  signature : ι → Sign

attribute [class] PseudoEuclideanSpace

variable {𝕜 : Type _} [IsROrC 𝕜]
variable {ι : Type _} [Fintype ι] [DecidableEq ι]
variable {E : PseudoEuclideanSpace 𝕜 ι}

instance PseudoEuclideanInnerProduct (E : PseudoEuclideanSpace 𝕜 ι) : Inner 𝕜 (ι → 𝕜) :=
  ⟨ fun (v w : ι → 𝕜) => ∑ i, conj (v i) * (w i) * ofReal (E.signature (i)) ⟩

lemma inner_eval {E : PseudoEuclideanSpace 𝕜 ι} (v w : ι → 𝕜) :
  (PseudoEuclideanInnerProduct E).inner v w = ∑ i, conj (v i) * (w i) * ofReal (E.signature (i)) :=
  by rfl

instance instPseudoInnerProductSpaceofPseudoEuclideanSpace (E : PseudoEuclideanSpace 𝕜 ι) :
  PseudoInnerProductSpace 𝕜 (ι → 𝕜) where
  inner := (PseudoEuclideanInnerProduct E).inner
  conj_symm := by
    intro x y
    rw [inner_eval, inner_eval, map_sum]
    apply congrArg (Finset.sum Finset.univ)
    ext i
    rw [map_mul, map_mul, conj_ofReal, conj_conj]
    simp [mul_comm]
  add_left := by
    intro x y z
    rw [inner_eval, inner_eval, inner_eval, ← Finset.sum_add_distrib]
    apply congrArg
    ext i
    sorry
  smul_left := sorry
  nondeg := sorry

namespace PseudoEuclideanSpace

local notation "⟪" x ", " y "⟫" => @inner 𝕜 (ι → 𝕜) (PseudoEuclideanInnerProduct E) x y

variable (x y : ι → 𝕜)
#check ⟪x, y⟫

end PseudoEuclideanSpace