import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Group.Subgroup.Ker
variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]
@[ext]
structure SemidirectProduct (φ : G →* MulAut N) where
  left : N
  right : G
  deriving DecidableEq
attribute [nolint simpNF] SemidirectProduct.mk.injEq
attribute [nolint simpNF] SemidirectProduct.mk.sizeOf_spec
@[inherit_doc]
notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ
namespace SemidirectProduct
variable {N G}
variable {φ : G →* MulAut N}
instance : Mul (SemidirectProduct N G φ) where
  mul a b := ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩
lemma mul_def (a b : SemidirectProduct N G φ) : a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩ := rfl
@[simp]
theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left := rfl
@[simp]
theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right := rfl
instance : One (SemidirectProduct N G φ) where one := ⟨1, 1⟩
@[simp]
theorem one_left : (1 : N ⋊[φ] G).left = 1 := rfl
@[simp]
theorem one_right : (1 : N ⋊[φ] G).right = 1 := rfl
instance : Inv (SemidirectProduct N G φ) where
  inv x := ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩
@[simp]
theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹ := rfl
@[simp]
theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ := rfl
instance : Group (N ⋊[φ] G) where
  mul_assoc a b c := SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)
instance : Inhabited (N ⋊[φ] G) := ⟨1⟩
def inl : N →* N ⋊[φ] G where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]
@[simp]
theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n := rfl
@[simp]
theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 := rfl
theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩
@[simp]
theorem inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
  inl_injective.eq_iff
def inr : G →* N ⋊[φ] G where
  toFun g := ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp
@[simp]
theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 := rfl
@[simp]
theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g := rfl
theorem inr_injective : Function.Injective (inr : G → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩
@[simp]
theorem inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
  inr_injective.eq_iff
theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ := by
  ext <;> simp
theorem inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g := by
  rw [← MonoidHom.map_inv, inl_aut, inv_inv]
@[simp]
theorem mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g := by ext <;> simp
@[simp]
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x := by ext <;> simp
def rightHom : N ⋊[φ] G →* G where
  toFun := SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl
@[simp]
theorem rightHom_eq_right : (rightHom : N ⋊[φ] G → G) = right := rfl
@[simp]
theorem rightHom_comp_inl : (rightHom : N ⋊[φ] G →* G).comp inl = 1 := by ext; simp [rightHom]
@[simp]
theorem rightHom_comp_inr : (rightHom : N ⋊[φ] G →* G).comp inr = MonoidHom.id _ := by
  ext; simp [rightHom]
@[simp]
theorem rightHom_inl (n : N) : rightHom (inl n : N ⋊[φ] G) = 1 := by simp [rightHom]
@[simp]
theorem rightHom_inr (g : G) : rightHom (inr g : N ⋊[φ] G) = g := by simp [rightHom]
theorem rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G → G) :=
  Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩
theorem range_inl_eq_ker_rightHom : (inl : N →* N ⋊[φ] G).range = rightHom.ker :=
  le_antisymm (fun _ ↦ by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx ↦ ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩
section lift
variable (f₁ : N →* H) (f₂ : G →* H)
  (h : ∀ g, f₁.comp (φ g).toMonoidHom = (MulAut.conj (f₂ g)).toMonoidHom.comp f₁)
def lift (f₁ : N →* H) (f₂ : G →* H)
    (h : ∀ g, f₁.comp (φ g).toMonoidHom = (MulAut.conj (f₂ g)).toMonoidHom.comp f₁) :
    N ⋊[φ] G →* H where
  toFun a := f₁ a.1 * f₂ a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g ↦ DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]
@[simp]
theorem lift_inl (n : N) : lift f₁ f₂ h (inl n) = f₁ n := by simp [lift]
@[simp]
theorem lift_comp_inl : (lift f₁ f₂ h).comp inl = f₁ := by ext; simp
@[simp]
theorem lift_inr (g : G) : lift f₁ f₂ h (inr g) = f₂ g := by simp [lift]
@[simp]
theorem lift_comp_inr : (lift f₁ f₂ h).comp inr = f₂ := by ext; simp
theorem lift_unique (F : N ⋊[φ] G →* H) :
    F = lift (F.comp inl) (F.comp inr) fun _ ↦ by ext; simp [inl_aut] := by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]
theorem hom_ext {f g : N ⋊[φ] G →* H} (hl : f.comp inl = g.comp inl)
    (hr : f.comp inr = g.comp inr) : f = g := by
  rw [lift_unique f, lift_unique g]
  simp only [*]
end lift
section Map
variable {N₁ : Type*} {G₁ : Type*} [Group N₁] [Group G₁] {φ₁ : G₁ →* MulAut N₁}
def map (f₁ : N →* N₁) (f₂ : G →* G₁)
    (h : ∀ g : G, f₁.comp (φ g).toMonoidHom = (φ₁ (f₂ g)).toMonoidHom.comp f₁) :
    N ⋊[φ] G →* N₁ ⋊[φ₁] G₁ where
  toFun x := ⟨f₁ x.1, f₂ x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all
variable (f₁ : N →* N₁) (f₂ : G →* G₁)
  (h : ∀ g : G, f₁.comp (φ g).toMonoidHom = (φ₁ (f₂ g)).toMonoidHom.comp f₁)
@[simp]
theorem map_left (g : N ⋊[φ] G) : (map f₁ f₂ h g).left = f₁ g.left := rfl
@[simp]
theorem map_right (g : N ⋊[φ] G) : (map f₁ f₂ h g).right = f₂ g.right := rfl
@[simp]
theorem rightHom_comp_map : rightHom.comp (map f₁ f₂ h) = f₂.comp rightHom := rfl
@[simp]
theorem map_inl (n : N) : map f₁ f₂ h (inl n) = inl (f₁ n) := by simp [map]
@[simp]
theorem map_comp_inl : (map f₁ f₂ h).comp inl = inl.comp f₁ := by ext <;> simp
@[simp]
theorem map_inr (g : G) : map f₁ f₂ h (inr g) = inr (f₂ g) := by simp [map]
@[simp]
theorem map_comp_inr : (map f₁ f₂ h).comp inr = inr.comp f₂ := by ext <;> simp [map]
end Map
end SemidirectProduct