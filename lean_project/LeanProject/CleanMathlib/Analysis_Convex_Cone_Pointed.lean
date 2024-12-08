import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Module.Submodule.Basic
variable {𝕜 E F G : Type*}
local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}
abbrev PointedCone (𝕜 E) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :=
  Submodule {c : 𝕜 // 0 ≤ c} E
namespace PointedCone
open Function
section Definitions
variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
@[coe]
def toConvexCone (S : PointedCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := S
  smul_mem' c hc _ hx := S.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := S.add_mem hx hy
instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) where
  coe := toConvexCone
theorem toConvexCone_injective : Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) :=
  fun _ _ => by simp [toConvexCone]
@[simp]
theorem toConvexCone_pointed (S : PointedCone 𝕜 E) : (S : ConvexCone 𝕜 E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]
@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
instance instZero (S : PointedCone 𝕜 E) : Zero S :=
  ⟨0, S.zero_mem⟩
def _root_.ConvexCone.toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) : PointedCone 𝕜 E where
  carrier := S
  add_mem' hx hy := S.add_mem hx hy
  zero_mem' := hS
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    cases' eq_or_lt_of_le hc with hzero hpos
    · unfold ConvexCone.Pointed at hS
      convert hS
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert hpos
      · exact hx
@[simp]
lemma _root_.ConvexCone.mem_toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) (x : E) :
    x ∈ S.toPointedCone hS ↔ x ∈ S :=
  Iff.rfl
@[simp, norm_cast]
lemma _root_.ConvexCone.coe_toPointedCone {S : ConvexCone 𝕜 E} (hS : S.Pointed) :
    S.toPointedCone hS = S :=
  rfl
instance canLift : CanLift (ConvexCone 𝕜 E) (PointedCone 𝕜 E) (↑) ConvexCone.Pointed where
  prf S hS := ⟨S.toPointedCone hS, rfl⟩
end Definitions
section Maps
variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable [AddCommMonoid G] [Module 𝕜 G]
def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F :=
  Submodule.map (f : E →ₗ[𝕜≥0] F) S
@[simp, norm_cast]
theorem toConvexCone_map (S : PointedCone 𝕜 E) (f : E →ₗ[𝕜] F) :
    (S.map f : ConvexCone 𝕜 F) = (S : ConvexCone 𝕜 E).map f :=
  rfl
@[simp, norm_cast]
theorem coe_map (S : PointedCone 𝕜 E) (f : E →ₗ[𝕜] F) : (S.map f : Set F) = f '' S :=
  rfl
@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl
theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image g f S
@[simp]
theorem map_id (S : PointedCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| Set.image_id _
def comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : PointedCone 𝕜 E :=
  Submodule.comap (f : E →ₗ[𝕜≥0] F) S
@[simp, norm_cast]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl
@[simp]
theorem comap_id (S : PointedCone 𝕜 E) : S.comap LinearMap.id = S :=
  rfl
theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
end Maps
section PositiveCone
variable (𝕜 E)
variable [OrderedSemiring 𝕜]
variable [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]
def positive : PointedCone 𝕜 E :=
  (ConvexCone.positive 𝕜 E).toPointedCone <| ConvexCone.pointed_positive 𝕜 E
@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl
@[simp, norm_cast]
theorem toConvexCone_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl
end PositiveCone
section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def dual (S : PointedCone ℝ E) : PointedCone ℝ E :=
  ((S : Set E).innerDualCone).toPointedCone <| pointed_innerDualCone (S : Set E)
@[simp, norm_cast]
theorem toConvexCone_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl
open scoped InnerProductSpace in
@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  rfl
end Dual
end PointedCone