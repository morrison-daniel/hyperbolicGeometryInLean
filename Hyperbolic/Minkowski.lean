import Hyperbolic.PseudoEuclideanSpace
import Hyperbolic.Arcosh

open BigOperators ComplexConjugate PseudoInnerProductSpace PseudoEuclideanSpace

def MinkowskiSpace (d : ℕ+) : PseudoEuclideanSpace ℝ (Fin d) where
  signature := fun i => if (i : ℕ) = 0 then Sign.Minus else Sign.Plus

noncomputable instance (d : ℕ+) : PseudoInnerProductSpace ℝ (Fin d → ℝ) :=
  instPseudoInnerProductSpaceofPseudoEuclideanSpace (MinkowskiSpace d)

variable {d : ℕ+}

local notation "M" => Fin d → ℝ
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

def TimeLike (v : M)      : Prop := ⟪v, v⟫ <  0
def UnitTimeLike (v : M)  : Prop := ⟪v, v⟫ = -1
def LightLike (v : M)     : Prop := ⟪v, v⟫ =  0
def SpaceLike (v : M)     : Prop := ⟪v, v⟫ >  0
def UnitSpaceLike (v : M) : Prop := ⟪v, v⟫ =  1

def Future (v : M) : Prop := v 0 > 0

def Hyperboloid (v : M) : Prop := UnitTimeLike v ∧ Future v

noncomputable def hdist (v w : M) {_ : Hyperboloid v} {_ : Hyperboloid w} : M → M → ℝ :=
  fun v w => Real.arcosh (- ⟪v, w⟫)

namespace MinkowskiSpace

lemma inner_symm {x y : M} : ⟪x, y⟫ = ⟪y, x⟫ := by
  rw [← PseudoInnerProductSpace.inner_conj_symm x y]
  rfl

theorem tl_of_utl (v : M) {h : UnitTimeLike v} : TimeLike v := by
  rw [UnitTimeLike] at h
  rw [TimeLike, h]
  exact neg_one_lt_zero

theorem sl_of_usl (v : M) {h : UnitSpaceLike v} : SpaceLike v := by
  rw [UnitSpaceLike] at h
  rw [SpaceLike, h]
  exact zero_lt_one

def origin : M := fun i => if (i : ℕ) = 0 then 1 else 0

end MinkowskiSpace

namespace MinkowskiFour

local notation "M4" => Fin 4 → ℝ



end MinkowskiFour