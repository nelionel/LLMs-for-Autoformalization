import Mathlib.GroupTheory.Perm.Basic
assert_not_exists MonoidWithZero
variable {A : Type*} {M : Type*} {G : Type*}
@[reducible, to_additive "The group of additive automorphisms."]
def MulAut (M : Type*) [Mul M] :=
  M ≃* M
attribute [reducible] AddAut
namespace MulAut
variable (M) [Mul M]
instance : Group (MulAut M) where
  mul g h := MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm
instance : Inhabited (MulAut M) :=
  ⟨1⟩
@[simp]
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
@[simp]
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl
theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl
theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl
@[simp]
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl
@[simp]
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl
@[simp]
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _
@[simp]
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _
def toPerm : MulAut M →* Equiv.Perm M where
  toFun := MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
instance applyMulAction {M} [Monoid M] : MulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[simp]
protected theorem smul_def {M} [Monoid M] (f : MulAut M) (a : M) : f • a = f a :=
  rfl
instance apply_faithfulSMul {M} [Monoid M] : FaithfulSMul (MulAut M) M :=
  ⟨ fun h => MulEquiv.ext h ⟩
def conj [Group G] : G →* MulAut G where
  toFun g :=
    { toFun := fun h => g * h * g⁻¹
      invFun := fun h => g⁻¹ * h * g
      left_inv := fun _ => by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      right_inv := fun _ => by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      map_mul' := by simp only [mul_assoc, inv_mul_cancel_left, forall_const] }
  map_mul' g₁ g₂ := by
    ext h
    show g₁ * g₂ * h * (g₁ * g₂)⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * g₁⁻¹
    simp only [mul_assoc, mul_inv_rev]
  map_one' := by ext; simp only [one_mul, inv_one, mul_one, one_apply]; rfl
@[simp]
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl
@[simp]
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl
@[simp]
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl
@[simps]
def congr [Group G] {H : Type*} [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]
end MulAut
namespace AddAut
variable (A) [Add A]
instance group : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm
instance : Inhabited (AddAut A) :=
  ⟨1⟩
@[simp]
theorem coe_mul (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
@[simp]
theorem coe_one : ⇑(1 : AddAut A) = id :=
  rfl
theorem mul_def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
theorem one_def : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl
theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl
@[simp]
theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl
@[simp]
theorem one_apply (a : A) : (1 : AddAut A) a = a :=
  rfl
@[simp]
theorem apply_inv_self (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _
@[simp]
theorem inv_apply_self (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _
def toPerm : AddAut A →* Equiv.Perm A where
  toFun := AddEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
instance applyMulAction {A} [AddMonoid A] : MulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[simp]
protected theorem smul_def {A} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a :=
  rfl
instance apply_faithfulSMul {A} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
def conj [AddGroup G] : G →+ Additive (AddAut G) where
  toFun g :=
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g
        invFun := fun h => -g + h + g
        left_inv := fun _ => by
          simp only [add_assoc, neg_add_cancel_left, neg_add_cancel, add_zero]
        right_inv := fun _ => by
          simp only [add_assoc, add_neg_cancel_left, add_neg_cancel, add_zero]
        map_add' := by simp only [add_assoc, neg_add_cancel_left, forall_const] }
  map_add' g₁ g₂ := by
    apply Additive.toMul.injective; ext h
    show g₁ + g₂ + h + -(g₁ + g₂) = g₁ + (g₂ + h + -g₂) + -g₁
    simp only [add_assoc, neg_add_rev]
  map_zero' := by
    apply Additive.toMul.injective; ext
    simp only [zero_add, neg_zero, add_zero, toMul_ofMul, toMul_zero, one_apply]
    rfl
@[simp]
theorem conj_apply [AddGroup G] (g h : G) : conj g h = g + h + -g :=
  rfl
@[simp]
theorem conj_symm_apply [AddGroup G] (g h : G) : (conj g).symm h = -g + h + g :=
  rfl
@[simp]
theorem conj_inv_apply [AddGroup G] (g h : G) : (conj g).toMul⁻¹ h = -g + h + g :=
  rfl
@[simps]
def congr [AddGroup G] {H : Type*} [AddGroup H] (ϕ : G ≃+ H) :
    AddAut G ≃* AddAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]
end AddAut