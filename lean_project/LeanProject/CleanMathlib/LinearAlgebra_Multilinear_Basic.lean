import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Abel
open Fin Function Finset Set
universe uR uS uι v v' v₁ v₂ v₃
variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}
structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
  [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  toFun : (∀ i, M₁ i) → M₂
  map_update_add' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  map_update_smul' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)
attribute [nolint simpNF] MultilinearMap.mk.injEq
namespace MultilinearMap
section Semiring
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)
instance : FunLike (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl
initialize_simps_projections MultilinearMap (toFun → apply)
@[simp]
theorem toFun_eq_coe : f.toFun = ⇑f :=
  rfl
@[simp]
theorem coe_mk (f : (∀ i, M₁ i) → M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f :=
  rfl
theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : ∀ i, M₁ i) : f x = g x :=
  DFunLike.congr_fun h x
nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : ∀ i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
theorem coe_injective : Injective ((↑) : MultilinearMap R M₁ M₂ → (∀ i, M₁ i) → M₂) :=
  DFunLike.coe_injective
@[norm_cast]
theorem coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (∀ i, M₁ i) → M₂) = g ↔ f = g :=
  DFunLike.coe_fn_eq
@[ext]
theorem ext {f f' : MultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H
@[simp]
theorem mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) :
    (⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f := rfl
@[simp]
protected theorem map_update_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y
@[deprecated (since := "2024-11-03")] protected alias map_add := MultilinearMap.map_update_add
@[deprecated (since := "2024-11-03")] protected alias map_add' := MultilinearMap.map_update_add
@[simp]
protected theorem map_update_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x
@[deprecated (since := "2024-11-03")] protected alias map_smul := MultilinearMap.map_update_smul
@[deprecated (since := "2024-11-03")] protected alias map_smul' := MultilinearMap.map_update_smul
theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 := by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m, h, ← this, f.map_update_smul, zero_smul R (M := M₂)]
@[simp]
theorem map_update_zero [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : f (update m i 0) = 0 :=
  f.map_coord_zero i (update_same i 0 m)
@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : ∃ i : ι, i ∈ Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl
instance : Add (MultilinearMap R M₁ M₂) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩
@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
  rfl
instance : Zero (MultilinearMap R M₁ M₂) :=
  ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩
instance : Inhabited (MultilinearMap R M₁ M₂) :=
  ⟨0⟩
@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : MultilinearMap R M₁ M₂) m = 0 :=
  rfl
section SMul
variable {R' A : Type*} [Monoid R'] [Semiring A] [∀ i, Module A (M₁ i)] [DistribMulAction R' M₂]
  [Module A M₂] [SMulCommClass A R' M₂]
instance : SMul R' (MultilinearMap A M₁ M₂) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩
@[simp]
theorem smul_apply (f : MultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
  rfl
theorem coe_smul (c : R') (f : MultilinearMap A M₁ M₂) : ⇑(c • f) = c • (⇑ f) :=
  rfl
end SMul
instance addCommMonoid : AddCommMonoid (MultilinearMap R M₁ M₂) :=
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
@[simps] def coeAddMonoidHom : MultilinearMap R M₁ M₂ →+ (((i : ι) → M₁ i) → M₂) where
  toFun := DFunLike.coe; map_zero' := rfl; map_add' _ _ := rfl
@[simp]
theorem coe_sum {α : Type*} (f : α → MultilinearMap R M₁ M₂) (s : Finset α) :
    ⇑(∑ a ∈ s, f a) = ∑ a ∈ s, ⇑(f a) :=
  map_sum coeAddMonoidHom f s
theorem sum_apply {α : Type*} (f : α → MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) {s : Finset α} :
    (∑ a ∈ s, f a) m = ∑ a ∈ s, f a m := by simp
@[simps]
def toLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ where
  toFun x := f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp
@[simps]
def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) :
    MultilinearMap R M₁ (M₂ × M₃) where
  toFun m := (f m, g m)
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp
@[simps]
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (∀ i, M' i) where
  toFun m i := f i m
  map_update_add' _ _ _ _ := funext fun j => (f j).map_update_add _ _ _ _
  map_update_smul' _ _ _ _ := funext fun j => (f j).map_update_smul _ _ _ _
section
variable (R M₂ M₃)
@[simps]
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ MultilinearMap R (fun _ : ι ↦ M₂) M₃ where
  toFun f :=
    { toFun := fun x ↦ f (x i)
      map_update_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_update_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x ↦ f fun _ ↦ x
      map_add' := fun x y ↦ by
        simpa [update_eq_const_of_subsingleton] using f.map_update_add 0 i x y
      map_smul' := fun c x ↦ by
        simpa [update_eq_const_of_subsingleton] using f.map_update_smul 0 i c x }
  left_inv _ := rfl
  right_inv f := by ext x; refine congr_arg f ?_; exact (eq_const_of_subsingleton _ _).symm
variable (M₁) {M₂}
@[simps (config := .asFn)]
def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_update_add' _ := isEmptyElim
  map_update_smul' _ := isEmptyElim
end
def restr {k n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
    (hk : #s = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ where
  toFun v := f fun j => if h : j ∈ s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_update_add' v i x y := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
  map_update_smul' v i c x := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
theorem cons_add (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) := by
  simp_rw [← update_cons_zero x m (x + y), f.map_update_add, update_cons_zero]
theorem cons_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R) (x : M 0) :
    f (cons (c • x) m) = c • f (cons x m) := by
  simp_rw [← update_cons_zero x m (c • x), f.map_update_smul, update_cons_zero]
theorem snoc_add (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  simp_rw [← update_snoc_last x m (x + y), f.map_update_add, update_snoc_last]
theorem snoc_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M (castSucc i)) (c : R)
    (x : M (last n)) : f (snoc m (c • x)) = c • f (snoc m x) := by
  simp_rw [← update_snoc_last x m (c • x), f.map_update_smul, update_snoc_last]
section
variable {M₁' : ι → Type*} [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]
variable {M₁'' : ι → Type*} [∀ i, AddCommMonoid (M₁'' i)] [∀ i, Module R (M₁'' i)]
def compLinearMap (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    MultilinearMap R M₁ M₂ where
  toFun m := g fun i => f i (m i)
  map_update_add' m i x y := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_update_smul' m i c x := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
@[simp]
theorem compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i)
    (m : ∀ i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i) :=
  rfl
theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl
@[simp]
theorem zero_compLinearMap (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl
@[simp]
theorem compLinearMap_id (g : MultilinearMap R M₁' M₂) :
    (g.compLinearMap fun _ => LinearMap.id) = g :=
  ext fun _ => rfl
theorem compLinearMap_injective (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)
theorem compLinearMap_inj (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i))
    (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff
@[simp]
theorem comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i →ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i →ₗ[R] M₁' i)
  rw [← zero_compLinearMap f', compLinearMap_inj f' fun i => (f i).surjective]
end
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') := by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j ∈ t <;> simp [m'', h, hit, h']
  rw [A, f.map_update_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.not_mem_of_mem_powerset_of_not_mem hs hit]
    · by_cases h' : j ∈ s <;> simp [m'', h, h']
  rw [this]
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ
section ApplySum
variable {α : ι → Type*} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))
open Fintype Finset
theorem map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : ℕ} (h : (∑ i, #(A i)) = n) :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) := by
  letI := fun i => Classical.decEq (α i)
  induction' n using Nat.strong_induction_on with n IH generalizing A
  by_cases Ai_empty : ∃ i, A i = ∅
  · obtain ⟨i, hi⟩ : ∃ i, ∑ j ∈ A i, g i j = 0 := Ai_empty.imp fun i hi ↦ by simp [hi]
    have hpi : piFinset A = ∅ := by simpa
    rw [f.map_coord_zero i hi, hpi, Finset.sum_empty]
  push_neg at Ai_empty
  by_cases Ai_singleton : ∀ i, #(A i) ≤ 1
  · have Ai_card : ∀ i, #(A i) = 1 := by
      intro i
      have pos : #(A i) ≠ 0 := by simp [Finset.card_eq_zero, Ai_empty i]
      have : #(A i) ≤ 1 := Ai_singleton i
      exact le_antisymm this (Nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos))
    have :
      ∀ r : ∀ i, α i, r ∈ piFinset A → (f fun i => g i (r i)) = f fun i => ∑ j ∈ A i, g i j := by
      intro r hr
      congr with i
      have : ∀ j ∈ A i, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_piFinset.mp hr i
      simp only [Finset.sum_congr rfl this, Finset.mem_univ, Finset.sum_const, Ai_card i, one_nsmul]
    simp only [Finset.sum_congr rfl this, Ai_card, card_piFinset, prod_const_one, one_nsmul,
      Finset.sum_const]
  push_neg at Ai_singleton
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < #(A i) := Ai_singleton
  obtain ⟨j₁, j₂, _, hj₂, _⟩ : ∃ j₁ j₂, j₁ ∈ A i₀ ∧ j₂ ∈ A i₀ ∧ j₁ ≠ j₂ :=
    Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : ∀ i, B i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [B, sdiff_subset, update_same]
    · simp only [B, hi, update_noteq, Ne, not_false_iff, Finset.Subset.refl]
  have C_subset_A : ∀ i, C i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [C, hj₂, Finset.singleton_subset_iff, update_same]
    · simp only [C, hi, update_noteq, Ne, not_false_iff, Finset.Subset.refl]
  have A_eq_BC :
    (fun i => ∑ j ∈ A i, g i j) =
      Function.update (fun i => ∑ j ∈ A i, g i j) i₀
        ((∑ j ∈ B i₀, g i₀ j) + ∑ j ∈ C i₀, g i₀ j) := by
    ext i
    by_cases hi : i = i₀
    · rw [hi, update_same]
      have : A i₀ = B i₀ ∪ C i₀ := by
        simp only [B, C, Function.update_same, Finset.sdiff_union_self_eq_union]
        symm
        simp only [hj₂, Finset.singleton_subset_iff, Finset.union_eq_left]
      rw [this]
      refine Finset.sum_union <| Finset.disjoint_right.2 fun j hj => ?_
      have : j = j₂ := by
        simpa [C] using hj
      rw [this]
      simp only [B, mem_sdiff, eq_self_iff_true, not_true, not_false_iff, Finset.mem_singleton,
        update_same, and_false]
    · simp [hi]
  have Beq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ B i₀, g i₀ j) = fun i =>
      ∑ j ∈ B i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_same]
    · simp only [B, hi, update_noteq, Ne, not_false_iff]
  have Ceq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ C i₀, g i₀ j) = fun i =>
      ∑ j ∈ C i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_same]
    · simp only [C, hi, update_noteq, Ne, not_false_iff]
  have Brec : (f fun i => ∑ j ∈ B i, g i j) = ∑ r ∈ piFinset B, f fun i => g i (r i) := by
    have : ∑ i, #(B i) < ∑ i, #(A i) := by
      refine sum_lt_sum (fun i _ => card_le_card (B_subset_A i)) ⟨i₀, mem_univ _, ?_⟩
      have : {j₂} ⊆ A i₀ := by simp [hj₂]
      simp only [B, Finset.card_sdiff this, Function.update_same, Finset.card_singleton]
      exact Nat.pred_lt (ne_of_gt (lt_trans Nat.zero_lt_one hi₀))
    rw [h] at this
    exact IH _ this B rfl
  have Crec : (f fun i => ∑ j ∈ C i, g i j) = ∑ r ∈ piFinset C, f fun i => g i (r i) := by
    have : (∑ i, #(C i)) < ∑ i, #(A i) :=
      Finset.sum_lt_sum (fun i _ => Finset.card_le_card (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by simp [C, hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (piFinset B) (piFinset C) :=
    haveI : Disjoint (B i₀) (C i₀) := by simp [B, C]
    piFinset_disjoint_of_disjoint B C this
  have pi_BC : piFinset A = piFinset B ∪ piFinset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ C i₀ := by simp [C, hri₀]
          rwa [hi]
        · simp [C, hi, mem_piFinset.1 hr i]
      · apply Finset.mem_union_left
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ B i₀ := by simp [B, hri₀, mem_piFinset.1 hr i₀]
          rwa [hi]
        · simp [B, hi, mem_piFinset.1 hr i]
    · exact
        Finset.union_subset (piFinset_subset _ _ fun i => B_subset_A i)
          (piFinset_subset _ _ fun i => C_subset_A i)
  rw [A_eq_BC]
  simp only [MultilinearMap.map_update_add, Beq, Ceq, Brec, Crec, pi_BC]
  rw [← Finset.sum_union D]
theorem map_sum_finset [DecidableEq ι] [Fintype ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl
theorem map_sum [DecidableEq ι] [Fintype ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun _ => Finset.univ
theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M₁ i)
    (m : ∀ i, M₁ i) : f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) := by
  classical
    induction' t using Finset.induction with a t has ih h
    · simp
    · simp [Finset.sum_insert has, ih]
end ApplySum
@[simps]
def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    MultilinearMap R M₁ p where
  toFun v := ⟨f v, h v⟩
  map_update_add' _ _ _ _ := Subtype.ext <| MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' _ _ _ _ := Subtype.ext <| MultilinearMap.map_update_smul _ _ _ _ _
section RestrictScalar
variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]
def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' m i := (f.toLinearMap m i).map_smul_of_tower
@[simp]
theorem coe_restrictScalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
end RestrictScalar
section
variable {ι₁ ι₂ ι₃ : Type*}
@[simps apply]
def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun v := m fun i => v (σ i)
  map_update_add' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_add]
  map_update_smul' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_smul]
theorem domDomCongr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
theorem domDomCongr_mul (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]
@[simp]
theorem domDomCongr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq
end
lemma domDomRestrict_aux {ι} [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {M₁ : ι → Type*}
    [DecidableEq {a // P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // P a})
    (c : M₁ i) : (fun j ↦ if h : P j then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  ext j
  by_cases h : j = i
  · rw [h, Function.update_same]
    simp only [i.2, update_same, dite_true]
  · rw [Function.update_noteq h]
    by_cases h' : P j
    · simp only [h', ne_eq, Subtype.mk.injEq, dite_true]
      have h'' : ¬ ⟨j, h'⟩ = i :=
        fun he => by apply_fun (fun x => x.1) at he; exact h he
      rw [Function.update_noteq h'']
    · simp only [h', ne_eq, Subtype.mk.injEq, dite_false]
lemma domDomRestrict_aux_right {ι} [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {M₁ : ι → Type*}
    [DecidableEq {a // ¬ P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // ¬ P a})
    (c : M₁ i) : (fun j ↦ if h : P j then x ⟨j, h⟩ else Function.update z i c ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j ↦ x ⟨j.1, not_not.mp j.2⟩) i c
def domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P]
    (z : (i : {a : ι // ¬ P a}) → M₁ i) :
    MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂ where
  toFun x := f (fun j ↦ if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_update_add' x i a b := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_add]
  map_update_smul' z i c a := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_smul]
@[simp]
lemma domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι → Prop)
    [DecidablePred P] (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)
@[simp]
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]
end Semiring
end MultilinearMap
namespace LinearMap
variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M'] [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']
def compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp
@[simp]
theorem coe_compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    ⇑(g.compMultilinearMap f) = g ∘ f :=
  rfl
@[simp]
theorem compMultilinearMap_apply (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) :
    g.compMultilinearMap f m = g (f m) :=
  rfl
@[simp]
theorem compMultilinearMap_zero (g : M₂ →ₗ[R] M₃) :
    g.compMultilinearMap (0 : MultilinearMap R M₁ M₂) = 0 :=
  MultilinearMap.ext fun _ => map_zero g
@[simp]
theorem zero_compMultilinearMap (f: MultilinearMap R M₁ M₂) :
    (0 : M₂ →ₗ[R] M₃).compMultilinearMap f = 0 := rfl
@[simp]
theorem compMultilinearMap_add (g : M₂ →ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (f₁ + f₂) = g.compMultilinearMap f₁ + g.compMultilinearMap f₂ :=
  MultilinearMap.ext fun _ => map_add g _ _
@[simp]
theorem add_compMultilinearMap (g₁ g₂ : M₂ →ₗ[R] M₃) (f: MultilinearMap R M₁ M₂) :
    (g₁ + g₂).compMultilinearMap f = g₁.compMultilinearMap f + g₂.compMultilinearMap f := rfl
@[simp]
theorem compMultilinearMap_smul [Monoid S] [DistribMulAction S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₂] [SMulCommClass R S M₃] [CompatibleSMul M₂ M₃ S R]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (s • f) = s • g.compMultilinearMap f :=
  MultilinearMap.ext fun _ => g.map_smul_of_tower _ _
@[simp]
theorem smul_compMultilinearMap [Monoid S] [DistribMulAction S M₃] [SMulCommClass R S M₃]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    (s • g).compMultilinearMap f = s • g.compMultilinearMap f := rfl
@[simp]
theorem subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
    (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f :=
  rfl
@[simp]
theorem compMultilinearMap_codRestrict (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
    (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f =
      (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  rfl
variable {ι₁ ι₂ : Type*}
@[simp]
theorem compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
    (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp [MultilinearMap.domDomCongr]
end LinearMap
namespace MultilinearMap
section Semiring
variable [Semiring R] [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
  [AddCommMonoid M₂] [Module R M₂]
instance [Monoid S] [DistribMulAction S M₂] [Module R M₂] [SMulCommClass R S M₂] :
    DistribMulAction S (MultilinearMap R M₁ M₂) :=
  coe_injective.distribMulAction coeAddMonoidHom fun _ _ ↦ rfl
section Module
variable [Semiring S] [Module S M₂] [SMulCommClass R S M₂]
instance : Module S (MultilinearMap R M₁ M₂) :=
  coe_injective.module _ coeAddMonoidHom fun _ _ ↦ rfl
instance [NoZeroSMulDivisors S M₂] : NoZeroSMulDivisors S (MultilinearMap R M₁ M₂) :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul
variable [AddCommMonoid M₃] [Module S M₃] [Module R M₃] [SMulCommClass R S M₃]
variable (S) in
@[simps]
def _root_.LinearMap.compMultilinearMapₗ [Semiring S] [Module S M₂] [Module S M₃]
    [SMulCommClass R S M₂] [SMulCommClass R S M₃] [LinearMap.CompatibleSMul M₂ M₃ S R]
    (g : M₂ →ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ →ₗ[S] MultilinearMap R M₁ M₃ where
  toFun := g.compMultilinearMap
  map_add' := g.compMultilinearMap_add
  map_smul' := g.compMultilinearMap_smul
variable (R S M₁ M₂ M₃)
section OfSubsingleton
@[simps (config := { simpRhs := true })]
def ofSubsingletonₗ [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ₗ[S] MultilinearMap R (fun _ : ι ↦ M₂) M₃ :=
  { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
end OfSubsingleton
@[simps apply symm_apply]
def domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun f :=
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_update_add' := fun m i => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_symm_update, f.map_update_smul] }
  invFun f :=
    { toFun := f ∘ σ.piCongrLeft' M₁
      map_update_add' := fun m i => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_update, f.map_update_smul] }
  map_add' f₁ f₂ := by
    ext
    simp only [Function.comp, coe_mk, add_apply]
  map_smul' c f := by
    ext
    simp only [Function.comp, coe_mk, smul_apply, RingHom.id_apply]
  left_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.symm_apply_apply]
  right_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.apply_symm_apply]
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := ext fun _ => MultilinearMap.congr_arg f <| Subsingleton.elim _ _
@[simps apply symm_apply]
def domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }
end Module
end Semiring
section CommSemiring
variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)
section
variable {M₁' : ι → Type*} [Π i, AddCommMonoid (M₁' i)] [Π i, Module R (M₁' i)]
def domDomRestrictₗ (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P] :
    MultilinearMap R (fun (i : {a : ι // ¬ P a}) => M₁ i)
      (MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂) where
  toFun := fun z ↦ domDomRestrict f P z
  map_update_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_update_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]
lemma iteratedFDeriv_aux {ι} {M₁ : ι → Type*} {α : Type*} [DecidableEq α]
    (s : Set ι) [DecidableEq { x // x ∈ s }] (e : α ≃ s)
    (m : α → ((i : ι) → M₁ i)) (a : α) (z : (i : ι) → M₁ i) :
    (fun i ↦ update m a z (e.symm i) i) =
      (fun i ↦ update (fun j ↦ m (e.symm j) j) (e a) (z (e a)) i) := by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_same, update_same]
  · rw [update_noteq hne.symm, update_noteq fun h ↦ (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]
noncomputable def iteratedFDerivComponent {α : Type*}
    (f : MultilinearMap R M₁ M₂) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)] :
    MultilinearMap R (fun (i : {a : ι // a ∉ s}) ↦ M₁ i)
      (MultilinearMap R (fun (_ : α) ↦ (∀ i, M₁ i)) M₂) where
  toFun := fun z ↦
    { toFun := fun v ↦ domDomRestrictₗ f (fun i ↦ i ∈ s) z (fun i ↦ v (e.symm i) i)
      map_update_add' := by classical simp [iteratedFDeriv_aux]
      map_update_smul' := by classical simp [iteratedFDeriv_aux] }
  map_update_add' := by intros; ext; simp
  map_update_smul' := by intros; ext; simp
open Classical in
protected noncomputable def iteratedFDeriv [Fintype ι]
    (f : MultilinearMap R M₁ M₂) (k : ℕ) (x : (i : ι) → M₁ i) :
    MultilinearMap R (fun (_ : Fin k) ↦ (∀ i, M₁ i)) M₂ :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i ↦ x i)
@[simps] def compLinearMapₗ (f : Π (i : ι), M₁ i →ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := fun g ↦ g.compLinearMap f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl
@[simps] def compLinearMapMultilinear :
  @MultilinearMap R ι (fun i ↦ M₁ i →ₗ[R] M₁' i)
    ((MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂) _ _ _
      (fun _ ↦ LinearMap.module) _ where
  toFun := MultilinearMap.compLinearMapₗ
  map_update_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <|x j) + g fun j ↦ update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_update_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) with j j j
    · exact Function.apply_update c f i (f₁ + f₂) j
    · exact Function.apply_update c f i f₁ j
    · exact Function.apply_update c f i f₂ j
  map_update_smul' := by
    intro _ f i a f₀
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_update_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) with j j j
    · exact Function.apply_update c f i (a • f₀) j
    · exact Function.apply_update c f i f₀ j
@[simps!] def piLinearMap :
    MultilinearMap R M₁' M₂ →ₗ[R]
    MultilinearMap R (fun i ↦ M₁ i →ₗ[R] M₁' i) (MultilinearMap R M₁ M₂) where
  toFun g := (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by aesop
  map_smul' := by aesop
end
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m := by
  refine s.induction_on (by simp) ?_
  intro j s j_not_mem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_not_mem_s]
    · simp [h]
  rw [s.piecewise_insert, f.map_update_smul, A, Hrec]
  simp [j_not_mem_s, mul_smul]
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m := by
  classical simpa using map_piecewise_smul f c m Finset.univ
@[simp]
theorem map_update_smul_left [DecidableEq ι] [Fintype ι]
    (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have :
    f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i ∈ Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this
section
variable (R ι)
variable (A : Type*) [CommSemiring A] [Algebra R A] [Fintype ι]
protected def mkPiAlgebra : MultilinearMap R (fun _ : ι => A) A where
  toFun m := ∏ i, m i
  map_update_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i c x := by simp [Finset.prod_update_of_mem]
variable {R A ι}
@[simp]
theorem mkPiAlgebra_apply (m : ι → A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl
end
section
variable (R n)
variable (A : Type*) [Semiring A] [Algebra R A]
protected def mkPiAlgebraFin : MultilinearMap R (fun _ : Fin n => A) A where
  toFun m := (List.ofFn m).prod
  map_update_add' {dec} m i x y := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul, this,
      mul_add, add_mul]
  map_update_smul' {dec} m i c x := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, this]
variable {R A n}
@[simp]
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl
theorem mkPiAlgebraFin_apply_const (a : A) :
    (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by simp
end
def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f
@[simp]
theorem smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : ∀ i, M₁ i) :
    f.smulRight z m = f m • z :=
  rfl
variable (R ι)
protected def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun _ : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smulRight z
variable {R ι}
@[simp]
theorem mkPiRing_apply [Fintype ι] (z : M₂) (m : ι → R) :
    (MultilinearMap.mkPiRing R ι z : (ι → R) → M₂) m = (∏ i, m i) • z :=
  rfl
theorem mkPiRing_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) :
    MultilinearMap.mkPiRing R ι (f fun _ => 1) = f := by
  ext m
  have : m = fun i => m i • (1 : R) := by
    ext j
    simp
  conv_rhs => rw [this, f.map_smul_univ]
  rfl
theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · intro x
    simp [h]
theorem mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, MultilinearMap.zero_apply]
theorem mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]
end CommSemiring
section RangeAddCommGroup
variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)
instance : Neg (MultilinearMap R M₁ M₂) :=
  ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩
@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl
instance : Sub (MultilinearMap R M₁ M₂) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_update_smul, smul_sub]⟩⟩
@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
  rfl
instance : AddCommGroup (MultilinearMap R M₁ M₂) :=
  { MultilinearMap.addCommMonoid with
    neg_add_cancel := fun _ => MultilinearMap.ext fun _ => neg_add_cancel _
    sub_eq_add_neg := fun _ _ => MultilinearMap.ext fun _ => sub_eq_add_neg _ _
    zsmul := fun n f =>
      { toFun := fun m => n • f m
        map_update_add' := fun m i x y => by simp [smul_add]
        map_update_smul' := fun l i x d => by simp [← smul_comm x n (_ : M₂)] }
    zsmul_zero' := fun _ => MultilinearMap.ext fun _ => SubNegMonoid.zsmul_zero' _
    zsmul_succ' := fun _ _ => MultilinearMap.ext fun _ => SubNegMonoid.zsmul_succ' _ _
    zsmul_neg' := fun _ _ => MultilinearMap.ext fun _ => SubNegMonoid.zsmul_neg' _ _ }
end RangeAddCommGroup
section AddCommGroup
variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)
@[simp]
theorem map_update_neg [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x : M₁ i) :
    f (update m i (-x)) = -f (update m i x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← MultilinearMap.map_update_add, neg_add_cancel, f.map_coord_zero i (update_same i 0 m)]
@[deprecated (since := "2024-11-03")] protected alias map_neg := MultilinearMap.map_update_neg
@[simp]
theorem map_update_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, MultilinearMap.map_update_add, map_update_neg]
@[deprecated (since := "2024-11-03")] protected alias map_sub := MultilinearMap.map_update_sub
lemma map_update [DecidableEq ι] (x : (i : ι) → M₁ i) (i : ι) (v : M₁ i)  :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [map_update_sub, update_eq_self, sub_sub_cancel]
open Finset in
lemma map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) → M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i ∈ s, f (fun j ↦ if j ∈ s → j < i then a j else if i = j then a j - b j else b j) := by
  refine s.induction_on_min ?_ fun k s hk ih ↦ ?_
  · rw [Finset.piecewise_empty, sum_empty, sub_self]
  rw [Finset.piecewise_insert, map_update, ← sub_add, ih,
      add_comm, sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; ext i; split_ifs with h₁ h₂
    · rw [update_noteq, Finset.piecewise_eq_of_not_mem]
      · exact fun h ↦ (hk i h).not_lt (h₁ <| .inr h)
      · exact fun h ↦ (h₁ <| .inl h).ne h
    · cases h₂
      rw [update_same, s.piecewise_eq_of_not_mem _ _ (lt_irrefl _ <| hk k ·)]
    · push_neg at h₁
      rw [update_noteq (Ne.symm h₂), s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl; intro i hi; congr; ext j; congr 1; apply propext
    simp_rw [imp_iff_not_or, not_or]; apply or_congr_left'
    intro h; rw [and_iff_right]; rintro rfl; exact h (hk i hi)
lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) → M₁ i) (s : Finset ι) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i ∈ s, f
      fun j ↦ if j ∈ s then if j < i then a j else if j = i then a j - b j else b j else v j := by
  rw [← s.piecewise_idem_right b a, map_sub_map_piecewise]
  refine Finset.sum_congr rfl fun i hi ↦ congr_arg f <| funext fun j ↦ ?_
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ ↦ hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classical.not_imp.mpr ⟨hjs, hji⟩), if_neg hji]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, if_pos rfl, s.piecewise_eq_of_mem _ _ hi]
    · rw [if_neg hij, if_neg hij.symm]
  · rw [if_neg hjs, if_pos fun h ↦ (hjs h).elim, s.piecewise_eq_of_not_mem _ _ hjs]
open Finset in
lemma map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) → M₁ i) :
    f (x + h) = f x + f.linearDeriv x h + ∑ s with 2 ≤ #s, f (s.piecewise h x) := by
  rw [add_comm, map_add_univ, ← Finset.powerset_univ,
      ← sum_filter_add_sum_filter_not _ (2 ≤ #·)]
  simp_rw [not_le, Nat.lt_succ, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
    powersetCard_zero, powersetCard_one, sum_singleton, Finset.piecewise_empty, sum_map,
    Function.Embedding.coeFn_mk, Finset.piecewise_singleton, linearDeriv_apply, add_comm]
open Finset in
lemma map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) → M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s with 2 ≤ #s, (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← LinearMap.map_sub, add_sub_cancel_left, sum_sub_distrib]
end AddCommGroup
section CommSemiring
variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂]
protected def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun _ : ι => R) M₂ where
  toFun z := MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext m
    simp [smul_add]
  map_smul' c z := by
    ext m
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
end CommSemiring
end MultilinearMap
section Currying
open MultilinearMap
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]
def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ where
  toFun m := f (m 0) (tail m)
  map_update_add' := @fun dec m i x y => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_add, tail_update_zero, MultilinearMap.add_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x y
      rw [← succ_pred i h]
      intro x y
      rw [tail_update_succ, MultilinearMap.map_update_add, tail_update_succ, tail_update_succ]
  map_update_smul' := @fun dec m i c x => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_smul, tail_update_zero, MultilinearMap.smul_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x
      rw [← succ_pred i h]
      intro x
      rw [tail_update_succ, tail_update_succ, MultilinearMap.map_update_smul]
@[simp]
theorem LinearMap.uncurryLeft_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : ∀ i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x :=
    { toFun := fun m => f (cons x m)
      map_update_add' := @fun dec m i y y' => by
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp
      map_update_smul' := @fun dec m i y c => by
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp }
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x
@[simp]
theorem MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0)
    (m : ∀ i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl
@[simp]
theorem LinearMap.curry_uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i :
    Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f := by
  ext m x
  simp only [tail_cons, LinearMap.uncurryLeft_apply, MultilinearMap.curryLeft_apply]
  rw [cons_zero]
@[simp]
theorem MultilinearMap.uncurry_curryLeft (f : MultilinearMap R M M₂) :
    f.curryLeft.uncurryLeft = f := by
  ext m
  simp
variable (R M M₂)
def multilinearCurryLeftEquiv :
    MultilinearMap R M M₂ ≃ₗ[R] (M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) where
  toFun := MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft
variable {R M M₂}
def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ where
  toFun m := f (init m) (m (last n))
  map_update_add' {dec} m i x y := by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x y
      rw [(castSucc_castLT i h).symm]
      intro x y
      rw [init_update_castSucc, MultilinearMap.map_update_add, init_update_castSucc,
        init_update_castSucc, LinearMap.add_apply]
    · revert x y
      rw [eq_last_of_not_lt h]
      intro x y
      simp_rw [init_update_last, update_same, LinearMap.map_add]
  map_update_smul' {dec} m i c x := by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x
      rw [(castSucc_castLT i h).symm]
      intro x
      rw [init_update_castSucc, init_update_castSucc, MultilinearMap.map_update_smul,
        LinearMap.smul_apply]
    · revert x
      rw [eq_last_of_not_lt h]
      intro x
      simp_rw [update_same, init_update_last, map_smul]
@[simp]
theorem MultilinearMap.uncurryRight_apply
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂))
    (m : ∀ i, M i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun m :=
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }
  map_update_add' := @fun dec m i x y => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (x + y)) z) = f (snoc (update m i x) z) + f (snoc (update m i y) z)
    rw [snoc_update, snoc_update, snoc_update, f.map_update_add]
  map_update_smul' := @fun dec m i c x => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (c • x)) z) = c • f (snoc (update m i x) z)
    rw [snoc_update, snoc_update, f.map_update_smul]
@[simp]
theorem MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl
@[simp]
theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]
@[simp]
theorem MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) :
    f.curryRight.uncurryRight = f := by
  ext m
  simp
variable (R M M₂)
def multilinearCurryRightEquiv :
    MultilinearMap R M M₂ ≃ₗ[R]
      MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun := MultilinearMap.curryRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MultilinearMap.uncurryRight
  left_inv := MultilinearMap.uncurry_curryRight
  right_inv := MultilinearMap.curry_uncurryRight
namespace MultilinearMap
variable {ι' : Type*} {R M₂}
def currySum (f : MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂) :
    MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun u :=
    { toFun := fun v => f (Sum.elim u v)
      map_update_add' := fun v i x y => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_update_add]
      map_update_smul' := fun v i c x => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_update_smul] }
  map_update_add' u i x y :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, add_apply, ← Sum.update_elim_inl, f.map_update_add]
  map_update_smul' u i c x :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, smul_apply, ← Sum.update_elim_inl, f.map_update_smul]
@[simp]
theorem currySum_apply (f : MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂) (u : ι → M')
    (v : ι' → M') : f.currySum u v = f (Sum.elim u v) :=
  rfl
def uncurrySum (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂)) :
    MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂ where
  toFun u := f (u ∘ Sum.inl) (u ∘ Sum.inr)
  map_update_add' u i x y := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_update_add, add_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
  map_update_smul' u i c x := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_update_smul, smul_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
@[simp]
theorem uncurrySum_aux_apply
    (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂))
    (u : ι ⊕ ι' → M') : f.uncurrySum u = f (u ∘ Sum.inl) (u ∘ Sum.inr) :=
  rfl
variable (ι ι' R M₂ M')
def currySumEquiv :
    MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv f := ext fun u => by simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl
variable {ι ι' R M₂ M'}
@[simp]
theorem coe_currySumEquiv : ⇑(currySumEquiv R ι M₂ M' ι') = currySum :=
  rfl
@[simp]
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv R ι M₂ M' ι').symm = uncurrySum :=
  rfl
variable (R M₂ M')
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv R (Fin k) M₂ M' (Fin l))
variable {R M₂ M'}
@[simp]
theorem curryFinFinset_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k → M') (ml : Fin l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl
@[simp]
theorem curryFinFinset_symm_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_not_mem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)
@[simp]
theorem curryFinFinset_symm_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearEquiv.symm_apply_apply]
end MultilinearMap
end Currying
namespace MultilinearMap
section Submodule
variable [Ring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M'] [Module R M₂]
def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    SubMulAction R M₂ where
  carrier := f '' { v | ∀ i, v i ∈ p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    letI := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_same]
      exact (p i).smul_mem _ (hx i)
    · rw [update_noteq hij]
      exact hx j
    · rw [f.map_update_smul, update_eq_self]
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩
def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun _ => ⊤
end Submodule
end MultilinearMap
set_option linter.style.longFile 1900