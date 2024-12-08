import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct
variable (N E G : Type*)
structure AddGroupExtension [AddGroup N] [AddGroup E] [AddGroup G] where
  inl : N →+ E
  rightHom : E →+ G
  inl_injective : Function.Injective inl
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  rightHom_surjective : Function.Surjective rightHom
@[to_additive]
structure GroupExtension [Group N] [Group E] [Group G] where
  inl : N →* E
  rightHom : E →* G
  inl_injective : Function.Injective inl
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  rightHom_surjective : Function.Surjective rightHom
variable {N E G}
namespace AddGroupExtension
variable [AddGroup N] [AddGroup E] [AddGroup G] (S : AddGroupExtension N E G)
structure Equiv {E' : Type*} [AddGroup E'] (S' : AddGroupExtension N E' G) where
  toAddMonoidHom : E →+ E'
  inl_comm : toAddMonoidHom.comp S.inl = S'.inl
  rightHom_comm : S'.rightHom.comp toAddMonoidHom = S.rightHom
structure Splitting where
  sectionHom : G →+ E
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = AddMonoidHom.id G
end AddGroupExtension
namespace GroupExtension
variable [Group N] [Group E] [Group G] (S : GroupExtension N E G)
@[to_additive "The range of the inclusion map is a normal additive subgroup." ]
instance normal_inl_range : S.inl.range.Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker
@[to_additive (attr := simp)]
theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom, MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n
@[to_additive (attr := simp)]
theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl n
noncomputable def conjAct : E →* MulAut N where
  toFun e := (MonoidHom.ofInjective S.inl_injective).trans <|
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  rfl
@[to_additive]
structure Equiv {E' : Type*} [Group E'] (S' : GroupExtension N E' G) where
  toMonoidHom : E →* E'
  inl_comm : toMonoidHom.comp S.inl = S'.inl
  rightHom_comm : S'.rightHom.comp toMonoidHom = S.rightHom
@[to_additive]
structure Splitting where
  sectionHom : G →* E
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = MonoidHom.id G
@[to_additive]
instance : FunLike S.Splitting G E where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h
@[to_additive]
instance : MonoidHomClass S.Splitting G E where
  map_mul s := s.sectionHom.map_mul'
  map_one s := s.sectionHom.map_one'
@[to_additive
      "A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such
      that the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`."]
def IsConj (S : GroupExtension N E G) (s s' : S.Splitting) : Prop :=
  ∃ n : N, s.sectionHom = fun g ↦ S.inl n * s'.sectionHom g * (S.inl n)⁻¹
end GroupExtension
namespace SemidirectProduct
variable [Group G] [Group N] (φ : G →* MulAut N)
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom_surjective := rightHom_surjective
theorem toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl := rfl
theorem toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl
def inr_splitting : (toGroupExtension φ).Splitting where
  sectionHom := inr
  rightHom_comp_sectionHom := rightHom_comp_inr
end SemidirectProduct