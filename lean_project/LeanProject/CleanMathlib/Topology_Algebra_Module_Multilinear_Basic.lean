import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
open Function Fin Set
universe u v w w₁ w₁' w₂ w₃ w₄
variable {R : Type u} {ι : Type v} {n : ℕ} {M : Fin n.succ → Type w} {M₁ : ι → Type w₁}
  {M₁' : ι → Type w₁'} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄}
structure ContinuousMultilinearMap (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] extends MultilinearMap R M₁ M₂ where
  cont : Continuous toFun
attribute [inherit_doc ContinuousMultilinearMap] ContinuousMultilinearMap.cont
@[inherit_doc]
notation:25 M "[×" n "]→L[" R "] " M' => ContinuousMultilinearMap R (fun i : Fin n => M) M'
namespace ContinuousMultilinearMap
section Semiring
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)]
  [∀ i, AddCommMonoid (M₁' i)] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)] [Module R M₂] [Module R M₃]
  [Module R M₄] [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (M₁ i)]
  [∀ i, TopologicalSpace (M₁' i)] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]
  (f f' : ContinuousMultilinearMap R M₁ M₂)
theorem toMultilinearMap_injective :
    Function.Injective
      (ContinuousMultilinearMap.toMultilinearMap :
        ContinuousMultilinearMap R M₁ M₂ → MultilinearMap R M₁ M₂)
  | ⟨f, hf⟩, ⟨g, hg⟩, h => by subst h; rfl
instance funLike : FunLike (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective' _ _ h := toMultilinearMap_injective <| MultilinearMap.coe_injective h
instance continuousMapClass :
    ContinuousMapClass (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  map_continuous := ContinuousMultilinearMap.cont
def Simps.apply (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : ∀ i, M₁ i) : M₂ :=
  L₁ v
initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  toMultilinearMap_toFun → apply)
@[continuity]
theorem coe_continuous : Continuous (f : (∀ i, M₁ i) → M₂) :=
  f.cont
@[simp]
theorem coe_coe : (f.toMultilinearMap : (∀ i, M₁ i) → M₂) = f :=
  rfl
@[ext]
theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H
@[simp]
theorem map_update_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y
@[deprecated (since := "2024-11-03")]
protected alias map_add := ContinuousMultilinearMap.map_update_add
@[simp]
theorem map_update_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x
@[deprecated (since := "2024-11-03")]
protected alias map_smul := ContinuousMultilinearMap.map_update_smul
theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h
@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
instance : Zero (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩
instance : Inhabited (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨0⟩
@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : ContinuousMultilinearMap R M₁ M₂) m = 0 :=
  rfl
@[simp]
theorem toMultilinearMap_zero : (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0 :=
  rfl
section SMul
variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]
instance : SMul R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩
@[simp]
theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) :
    (c • f) m = c • f m :=
  rfl
@[simp]
theorem toMultilinearMap_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) :
    (c • f).toMultilinearMap = c • f.toMultilinearMap :=
  rfl
instance [SMulCommClass R' R'' M₂] : SMulCommClass R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩
instance [SMul R' R''] [IsScalarTower R' R'' M₂] :
    IsScalarTower R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
instance [DistribMulAction R'ᵐᵒᵖ M₂] [IsCentralScalar R' M₂] :
    IsCentralScalar R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
instance : MulAction R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl
end SMul
section ContinuousAdd
variable [ContinuousAdd M₂]
instance : Add (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩
@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
  rfl
@[simp]
theorem toMultilinearMap_add (f g : ContinuousMultilinearMap R M₁ M₂) :
    (f + g).toMultilinearMap = f.toMultilinearMap + g.toMultilinearMap :=
  rfl
instance addCommMonoid : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂) :=
  toMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
def applyAddHom (m : ∀ i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ →+ M₂ where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl
@[simp]
theorem sum_apply {α : Type*} (f : α → ContinuousMultilinearMap R M₁ M₂) (m : ∀ i, M₁ i)
    {s : Finset α} : (∑ a ∈ s, f a) m = ∑ a ∈ s, f a m :=
  map_sum (applyAddHom m) f s
end ContinuousAdd
@[simps!] def toContinuousLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
  { f.toMultilinearMap.toLinearMap m i with
    cont := f.cont.comp (continuous_const.update i continuous_id) }
def prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prod_mk g.cont }
@[simp]
theorem prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
    (m : ∀ i, M₁ i) : (f.prod g) m = (f m, g m) :=
  rfl
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) :
    ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  cont := continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap
@[simp]
theorem coe_pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) : ⇑(pi f) = fun m j => f j m :=
  rfl
theorem pi_apply {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) (m : ∀ i, M₁ i) (j : ι') : pi f m j = f j m :=
  rfl
@[simps! toMultilinearMap apply_coe]
def codRestrict (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    ContinuousMultilinearMap R M₁ p :=
  ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩
section
variable (R M₂ M₃)
@[simps! apply_toMultilinearMap apply_apply symm_apply_apply]
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →L[R] M₃) ≃ ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
    (map_continuous f).comp <| continuous_pi fun _ ↦ continuous_id⟩
  left_inv _ := rfl
  right_inv f := toMultilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap
variable (M₁) {M₂}
@[simps! toMultilinearMap apply]
def constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const
end
def compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄ :=
  { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
    cont := g.cont.comp <| continuous_pi fun j => (f j).cont.comp <| continuous_apply _ }
@[simp]
theorem compContinuousLinearMap_apply (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) (m : ∀ i, M₁ i) :
    g.compContinuousLinearMap f m = g fun i => f i <| m i :=
  rfl
def _root_.ContinuousLinearMap.compContinuousMultilinearMap (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }
@[simp]
theorem _root_.ContinuousLinearMap.compContinuousMultilinearMap_coe (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) :
    (g.compContinuousMultilinearMap f : (∀ i, M₁ i) → M₃) =
      (g : M₂ → M₃) ∘ (f : (∀ i, M₁ i) → M₂) := by
  ext m
  rfl
@[simps]
def piEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] :
    (∀ i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  toFun := ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
@[simps! toMultilinearMap apply]
nonrec def domDomCongr {ι' : Type*} (e : ι ≃ ι')
    (f : ContinuousMultilinearMap R (fun _ : ι => M₂) M₃) :
    ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toMultilinearMap := f.domDomCongr e
  cont := f.cont.comp <| continuous_pi fun _ => continuous_apply _
@[simps]
def domDomCongrEquiv {ι' : Type*} (e : ι ≃ ι') :
    ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ ≃
      ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toFun := domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp
section linearDeriv
variable [ContinuousAdd M₂] [DecidableEq ι] [Fintype ι] (x y : ∀ i, M₁ i)
def linearDeriv : (∀ i, M₁ i) →L[R] M₂ := ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)
@[simp]
lemma linearDeriv_apply : f.linearDeriv x y = ∑ i, f (Function.update x i (y i)) := by
  unfold linearDeriv toContinuousLinearMap
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Finset.sum_apply]
  rfl
end linearDeriv
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) :=
  f.toMultilinearMap.cons_add m x y
theorem cons_smul (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R)
    (x : M 0) : f (cons (c • x) m) = c • f (cons x m) :=
  f.toMultilinearMap.cons_smul m c x
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _
section ApplySum
open Fintype Finset
variable {α : ι → Type*} [Fintype ι] (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))
theorem map_sum_finset [DecidableEq ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _
theorem map_sum [DecidableEq ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum _
end ApplySum
section RestrictScalar
variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]
def restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  cont := f.cont
@[simp]
theorem coe_restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
end RestrictScalar
end Semiring
section Ring
variable [Ring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] (f f' : ContinuousMultilinearMap R M₁ M₂)
@[simp]
theorem map_update_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _
@[deprecated (since := "2024-11-03")]
protected alias map_sub := ContinuousMultilinearMap.map_update_sub
section TopologicalAddGroup
variable [TopologicalAddGroup M₂]
instance : Neg (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩
@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl
instance : Sub (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩
@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - f') m = f m - f' m :=
  rfl
instance : AddCommGroup (ContinuousMultilinearMap R M₁ M₂) :=
  toMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
end TopologicalAddGroup
end Ring
section CommSemiring
variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  (f : ContinuousMultilinearMap R M₁ M₂)
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _
end CommSemiring
section DistribMulAction
variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [∀ i, AddCommMonoid (M₁ i)]
  [AddCommMonoid M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]
instance [ContinuousAdd M₂] : DistribMulAction R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.distribMulAction
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective
    fun _ _ => rfl
end DistribMulAction
section Module
variable {R' A : Type*} [Semiring R'] [Semiring A] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [ContinuousAdd M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [Module R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
instance : Module R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.module _
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective fun _ _ => rfl
@[simps]
def toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ →ₗ[R'] MultilinearMap A M₁ M₂ where
  toFun := toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul
@[simps (config := { simpRhs := true })]
def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R' (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R' (M' i)] [∀ i, ContinuousConstSMul R' (M' i)] :
    (∀ i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (∀ i, M' i) :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
end Module
section CommAlgebra
variable (R ι) (A : Type*) [Fintype ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A]
protected def mkPiAlgebra : ContinuousMultilinearMap R (fun _ : ι => A) A where
  cont := continuous_finset_prod _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A
@[simp]
theorem mkPiAlgebra_apply (m : ι → A) : ContinuousMultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl
end CommAlgebra
section Algebra
variable (R n) (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [ContinuousMul A]
protected def mkPiAlgebraFin : A[×n]→L[R] A where
  cont := by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A
variable {R n A}
@[simp]
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    ContinuousMultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl
end Algebra
section SMulRight
variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [TopologicalSpace R] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  [ContinuousSMul R M₂] (f : ContinuousMultilinearMap R M₁ R) (z : M₂)
@[simps! toMultilinearMap apply]
def smulRight : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.smulRight z
  cont := f.cont.smul continuous_const
end SMulRight
section CommRing
variable {M : Type*}
variable [Fintype ι] [CommRing R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M]
variable [ContinuousMul R] [ContinuousSMul R M]
variable (R ι) in
protected def mkPiRing (z : M) : ContinuousMultilinearMap R (fun _ : ι => R) M :=
  (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z
@[simp]
theorem mkPiRing_apply (z : M) (m : ι → R) :
    (ContinuousMultilinearMap.mkPiRing R ι z : (ι → R) → M) m = (∏ i, m i) • z :=
  rfl
theorem mkPiRing_apply_one_eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R) M) :
    ContinuousMultilinearMap.mkPiRing R ι (f fun _ => 1) = f :=
  toMultilinearMap_injective f.toMultilinearMap.mkPiRing_apply_one_eq_self
theorem mkPiRing_eq_iff {z₁ z₂ : M} :
    ContinuousMultilinearMap.mkPiRing R ι z₁ = ContinuousMultilinearMap.mkPiRing R ι z₂ ↔
      z₁ = z₂ := by
  rw [← toMultilinearMap_injective.eq_iff]
  exact MultilinearMap.mkPiRing_eq_iff
theorem mkPiRing_zero : ContinuousMultilinearMap.mkPiRing R ι (0 : M) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, ContinuousMultilinearMap.zero_apply]
theorem mkPiRing_eq_zero_iff (z : M) : ContinuousMultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]
end CommRing
end ContinuousMultilinearMap