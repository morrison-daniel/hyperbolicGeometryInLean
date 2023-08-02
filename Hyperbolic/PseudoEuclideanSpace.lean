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

def PseudoEuclideanInnerProduct (E : PseudoEuclideanSpace 𝕜 ι) : Inner 𝕜 (ι → 𝕜) :=
  ⟨ fun (v w : ι → 𝕜) => ∑ i, conj (v i) * (w i) * ofReal (E.signature (i)) ⟩

lemma inner_eval {E : PseudoEuclideanSpace 𝕜 ι} (v w : ι → 𝕜) :
  (PseudoEuclideanInnerProduct E).inner v w = ∑ i, conj (v i) * (w i) * ofReal (E.signature (i)) :=
  by rfl

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
    sorry
  smul_left := sorry
  nondeg := sorry

namespace PseudoEuclideanSpace

variable {𝕜 : Type _} [IsROrC 𝕜]
variable {ι : Type _} [Fintype ι] [DecidableEq ι]
variable [E : PseudoEuclideanSpace 𝕜 ι]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 (ι → 𝕜) (PseudoEuclideanInnerProduct E) x y

def TimeLike (v : ι → 𝕜)      : Prop := re ⟪v, v⟫ <  0
def UnitTimeLike (v : ι → 𝕜)  : Prop := re ⟪v, v⟫ = -1
def LightLike (v : ι → 𝕜)     : Prop := re ⟪v, v⟫ =  0
def SpaceLike (v : ι → 𝕜)     : Prop := re ⟪v, v⟫ >  0
def UnitSpaceLike (v : ι → 𝕜) : Prop := re ⟪v, v⟫ =  1

theorem timelike_of_unittimelike {v : ι → 𝕜} (h : UnitTimeLike v) : TimeLike v := by
  rw [UnitTimeLike] at h
  rw [TimeLike, h]
  exact neg_one_lt_zero

theorem spacelike_of_unitspacelike {v : ι → 𝕜} (h : UnitSpaceLike v) : SpaceLike v := by
  rw [UnitSpaceLike] at h
  rw [SpaceLike, h]
  exact zero_lt_one

end PseudoEuclideanSpace