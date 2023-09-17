import Hyperbolic.PseudoEuclideanSpace

open BigOperators ComplexConjugate PseudoInnerProductSpace PseudoEuclideanSpace

variable {d : ℕ}

def MinkowskiSpace : PseudoEuclideanSpace ℝ (Fin d) where
  signature := fun i => if (i : ℕ) = 0 then Sign.Minus else Sign.Plus

noncomputable instance : PseudoInnerProductSpace ℝ (Fin d → ℝ) :=
  instPseudoInnerProductSpaceofPseudoEuclideanSpace MinkowskiSpace

local notation "E" => Fin d → ℝ
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

def TimeLike (v : E)      : Prop := ⟪v, v⟫ <  0
def UnitTimeLike (v : E)  : Prop := ⟪v, v⟫ = -1
def LightLike (v : E)     : Prop := ⟪v, v⟫ =  0
def SpaceLike (v : E)     : Prop := ⟪v, v⟫ >  0
def UnitSpaceLike (v : E) : Prop := ⟪v, v⟫ =  1

theorem tl_of_utl {v : E} (h : UnitTimeLike v) : TimeLike v := by
  rw [UnitTimeLike] at h
  rw [TimeLike, h]
  exact neg_one_lt_zero

theorem sl_of_usl {v : E} (h : UnitSpaceLike v) : SpaceLike v := by
  rw [UnitSpaceLike] at h
  rw [SpaceLike, h]
  exact zero_lt_one