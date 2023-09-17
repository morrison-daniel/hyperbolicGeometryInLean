import Hyperbolic.PseudoInnerProductSpace

open BigOperators ComplexConjugate IsROrC PseudoInnerProductSpace

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

namespace Sign

def Plus : Sign := ⟨  1, by left; rfl ⟩
def Minus : Sign := ⟨ -1, by right; rfl ⟩

end Sign

@[reducible]
structure PseudoEuclideanSpace (𝕜 : Type _) (ι : Type _)
  [IsROrC 𝕜] [Fintype ι] [DecidableEq ι] where
    signature : ι → Sign

attribute [class] PseudoEuclideanSpace

namespace PseudoEuclideanSpace

variable {𝕜 : Type _} [IsROrC 𝕜]
variable {ι : Type _} [Fintype ι] [DecidableEq ι]

def PseudoEuclideanInnerProduct (p : PseudoEuclideanSpace 𝕜 ι) : Inner 𝕜 (ι → 𝕜) :=
  ⟨ fun (v w : ι → 𝕜) => ∑ i, conj (v i) * (w i) * ofReal (p.signature (i)) ⟩

lemma inner_eval [p : PseudoEuclideanSpace 𝕜 ι] (v w : ι → 𝕜) :
  (PseudoEuclideanInnerProduct p).inner v w = ∑ i, conj (v i) * (w i) * ofReal (p.signature (i)) :=
  by rfl

lemma vec_add [PseudoEuclideanSpace 𝕜 ι] (v w : ι → 𝕜) (i : ι) : (v + w) i = v i + w i := rfl
lemma vec_smul [PseudoEuclideanSpace 𝕜 ι] (v : ι → 𝕜) (r : 𝕜) (i : ι) : (r • v) i = r * (v i) := rfl

def instPseudoInnerProductSpaceofPseudoEuclideanSpace (E : PseudoEuclideanSpace 𝕜 ι) :
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
    rw [vec_add, map_add, add_mul, add_mul]
  smul_left := by
    intro x y r
    rw [inner_eval, inner_eval, Finset.mul_sum]
    apply congrArg
    ext i
    rw [vec_smul, map_mul]
    nth_rw 1 [← mul_assoc, ← mul_assoc]
  nondeg := by
    intro x h
    ext i
    specialize h (fun j => if j = i then 1 else 0)
    rw [inner_eval] at h
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)] at h
    . rw [if_pos] at h
      simp at h
      rcases h with h | h
      . exact h
      . exfalso
        have cond : (PseudoEuclideanSpace.signature E i).1 = 1 ∨ (PseudoEuclideanSpace.signature E i).1 = -1 := 
          (PseudoEuclideanSpace.signature E i).2
        aesop
      . rfl
    . intro j _ hj
      rw [if_neg hj]
      simp

end PseudoEuclideanSpace