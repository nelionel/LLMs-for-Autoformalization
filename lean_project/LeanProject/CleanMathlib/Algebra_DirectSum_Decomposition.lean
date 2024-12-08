import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Basic
variable {ι R M σ : Type*}
open DirectSum
namespace DirectSum
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y ↦ by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩
abbrev Decomposition.ofAddHom (decompose : M →+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv
noncomputable def IsInternal.chooseDecomposition (h : IsInternal ℳ) :
    DirectSum.Decomposition ℳ where
  decompose' := (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv
variable [Decomposition ℳ]
protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv
protected theorem Decomposition.inductionOn {p : M → Prop} (h_zero : p 0)
    (h_homogeneous : ∀ {i} (m : ℳ i), p (m : M)) (h_add : ∀ m m' : M, p m → p m' → p (m + m')) :
    ∀ m, p m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (decompose ℳ).left_inv _
      right_inv := fun _ ↦ (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add
@[simp]
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl
@[simp]
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _
@[simp]
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _, Equiv.apply_symm_apply]
theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩
theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]
theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij, ZeroMemClass.coe_zero]
theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with map_add' := map_add (DirectSum.coeAddMonoidHom ℳ) }
@[simp]
lemma decomposeAddEquiv_apply (a : M) :
    decomposeAddEquiv ℳ a = decompose ℳ a := rfl
@[simp]
lemma decomposeAddEquiv_symm_apply (a : ⨁ i, ℳ i) :
    (decomposeAddEquiv ℳ).symm a = (decompose ℳ).symm a := rfl
@[simp]
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)
@[simp]
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm
@[simp]
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y
@[simp]
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y
@[simp]
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s
@[simp]
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s
theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]
end AddCommMonoid
instance addCommGroupSetLike [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ) :
    AddCommGroup (⨁ i, ℳ i) := by infer_instance
section AddCommGroup
variable [DecidableEq ι] [AddCommGroup M]
variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)
variable [Decomposition ℳ]
@[simp]
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x
@[simp]
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x
@[simp]
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y
@[simp]
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y
end AddCommGroup
section Module
variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)
abbrev Decomposition.ofLinearMap (decompose : M →ₗ[R] ⨁ i, ℳ i)
    (h_left_inv : DirectSum.coeLinearMap ℳ ∘ₗ decompose = .id)
    (h_right_inv : decompose ∘ₗ DirectSum.coeLinearMap ℳ = .id) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv
variable [Decomposition ℳ]
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }
@[simp] theorem decomposeLinearEquiv_apply (m : M) :
    decomposeLinearEquiv ℳ m = decompose ℳ m := rfl
@[simp] theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (decomposeLinearEquiv ℳ).symm m = (decompose ℳ).symm m := rfl
@[simp]
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x
@[simp] theorem decomposeLinearEquiv_symm_comp_lof (i : ι) :
    (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype :=
  LinearMap.ext <| decompose_symm_of _
theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M →ₗ[R] N⦄
    (h : ∀ i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g :=
  LinearMap.ext <| (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr <|
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) →ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]
end Module
end DirectSum