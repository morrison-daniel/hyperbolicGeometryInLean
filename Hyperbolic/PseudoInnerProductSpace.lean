import Mathlib.Analysis.InnerProductSpace.Basic

open ComplexConjugate IsROrC

class PseudoInnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] [AddCommGroup E] [Module 𝕜 E]
  extends Inner 𝕜 E where
  /-- The inner product is hermitian. --/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordintate. --/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. --/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
  /-- The inner product is nondegenerate. --/
  nondeg : ∀ x, (∀ y, inner x y = 0) → x = 0

namespace PseudoInnerProductSpace

variable {𝕜 E : Type _} [IsROrC 𝕜] [AddCommGroup E] [Module 𝕜 E] [PseudoInnerProductSpace 𝕜 E]
variable {F : Type _} [AddCommGroup F] [Module ℝ F] [PseudoInnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

@[simp]
theorem inner_conj_symm (x y : E) : conj ⟪x, y⟫ = ⟪y, x⟫ :=
  conj_symm _ _

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  add_left _ _ _

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]
  simp only [inner_conj_symm]

theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = conj r * ⟪x, y⟫ :=
  smul_left _ _ _

theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_symm]

@[simp]
theorem inner_self_re {x : E} : re ⟪x, x⟫ = ⟪x, x⟫ := by
  rw [re_eq_add_conj]; simp

@[simp]
theorem inner_self_im {x : E} : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]; simp

theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by
  rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = - im ⟪y, x⟫ := by
  rw [← inner_conj_symm, conj_im]

@[simp]
theorem inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 0, inner_smul_left, RingHom.map_zero, zero_mul]

@[simp]
theorem inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by
  rw [← zero_smul 𝕜 0, inner_smul_right, zero_mul]

@[simp]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]; simp

@[simp]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_nondeg_left (x : E) : (∀ y, ⟪x, y⟫ = 0) → x = 0 := nondeg x

theorem inner_nondeg_right (y : E) : (∀ x, ⟪x, y⟫ = 0) → y = 0 := by
  rintro hy
  apply @inner_nondeg_left 𝕜 _ _
  intro x
  specialize hy x
  rw [← inner_conj_symm, map_eq_zero]
  exact hy

@[simps!]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _

@[simp]
def bilinFormOfRealInner : BilinForm ℝ F where
  bilin := inner
  bilin_add_left := inner_add_left
  bilin_smul_left _a _x _y := inner_smul_left _ _ _
  bilin_add_right := inner_add_right
  bilin_smul_right _a _x _y := by rw [inner_smul_right]