import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use
open Function Set List
namespace CoxeterMatrix
variable {B B' : Type*} (M : CoxeterMatrix B) (e : B ≃ B')
def relation (i i' : B) : FreeGroup B := (FreeGroup.of i * FreeGroup.of i') ^ M i i'
def relationsSet : Set (FreeGroup B) := range <| uncurry M.relation
protected def Group : Type _ := PresentedGroup M.relationsSet
instance : Group M.Group := QuotientGroup.Quotient.group _
def simple (i : B) : M.Group := PresentedGroup.of i
theorem reindex_relationsSet :
    (M.reindex e).relationsSet =
    FreeGroup.freeGroupCongr e '' M.relationsSet := let M' := M.reindex e; calc
  Set.range (uncurry M'.relation)
  _ = Set.range (uncurry M'.relation ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range (FreeGroup.freeGroupCongr e ∘ uncurry M.relation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [relation, reindex_apply, M']
  _ = _ := by simp [Set.range_comp, relationsSet]
def reindexGroupEquiv : (M.reindex e).Group ≃* M.Group :=
  .symm <| QuotientGroup.congr
    (Subgroup.normalClosure M.relationsSet)
    (Subgroup.normalClosure (M.reindex e).relationsSet)
    (FreeGroup.freeGroupCongr e)
    (by
      rw [reindex_relationsSet,
        Subgroup.map_normalClosure _ _ (by simpa using (FreeGroup.freeGroupCongr e).surjective),
        MonoidHom.coe_coe])
theorem reindexGroupEquiv_apply_simple (i : B') :
    (M.reindexGroupEquiv e) ((M.reindex e).simple i) = M.simple (e.symm i) := rfl
theorem reindexGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexGroupEquiv e).symm (M.simple i) = (M.reindex e).simple (e i) := rfl
end CoxeterMatrix
section
variable {B : Type*} (M : CoxeterMatrix B)
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  mulEquiv : W ≃* M.Group
class IsCoxeterGroup.{u} (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ B : Type u, ∃ M : CoxeterMatrix B, Nonempty (CoxeterSystem M W)
def CoxeterMatrix.toCoxeterSystem : CoxeterSystem M M.Group := ⟨.refl _⟩
end
namespace CoxeterSystem
open CoxeterMatrix
variable {B B' : Type*} (e : B ≃ B')
variable {W H : Type*} [Group W] [Group H]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
@[simps]
protected def reindex (e : B ≃ B') : CoxeterSystem (M.reindex e) W :=
  ⟨cs.mulEquiv.trans (M.reindexGroupEquiv e).symm⟩
@[simps]
protected def map (e : W ≃* H) : CoxeterSystem M H := ⟨e.symm.trans cs.mulEquiv⟩
def simple (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)
@[simp]
theorem _root_.CoxeterMatrix.toCoxeterSystem_simple (M : CoxeterMatrix B) :
    M.toCoxeterSystem.simple = M.simple := rfl
@[simp] theorem reindex_simple (i' : B') : (cs.reindex e).simple i' = cs.simple (e.symm i') := rfl
@[simp] theorem map_simple (e : W ≃* H) (i : B) : (cs.map e).simple i = e (cs.simple i) := rfl
local prefix:100 "s" => cs.simple
@[simp]
theorem simple_mul_simple_self (i : B) : s i * s i = 1 := by
  have : (FreeGroup.of i) * (FreeGroup.of i) ∈ M.relationsSet := ⟨(i, i), by simp [relation]⟩
  have : (PresentedGroup.mk _ (FreeGroup.of i * FreeGroup.of i) : M.Group) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure this)
  unfold simple
  rw [← map_mul, PresentedGroup.of, map_mul]
  exact map_mul_eq_one cs.mulEquiv.symm this
@[simp]
theorem simple_mul_simple_cancel_right {w : W} (i : B) : w * s i * s i = w := by
  simp [mul_assoc]
@[simp]
theorem simple_mul_simple_cancel_left {w : W} (i : B) : s i * (s i * w) = w := by
  simp [← mul_assoc]
@[simp] theorem simple_sq (i : B) : s i ^ 2 = 1 := pow_two (s i) ▸ cs.simple_mul_simple_self i
@[simp]
theorem inv_simple (i : B) : (s i)⁻¹ = s i :=
  (eq_inv_of_mul_eq_one_right (cs.simple_mul_simple_self i)).symm
@[simp]
theorem simple_mul_simple_pow (i i' : B) : (s i * s i') ^ M i i' = 1 := by
  have : (FreeGroup.of i * FreeGroup.of i') ^ M i i' ∈ M.relationsSet := ⟨(i, i'), rfl⟩
  have : (PresentedGroup.mk _ ((FreeGroup.of i * FreeGroup.of i') ^ M i i') : M.Group) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure this)
  unfold simple
  rw [← map_mul, ← map_pow]
  exact (MulEquiv.map_eq_one_iff cs.mulEquiv.symm).mpr this
@[simp] theorem simple_mul_simple_pow' (i i' : B) : (s i' * s i) ^ M i i' = 1 :=
  M.symmetric i' i ▸ cs.simple_mul_simple_pow i' i
theorem subgroup_closure_range_simple : Subgroup.closure (range cs.simple) = ⊤ := by
  have : cs.simple = cs.mulEquiv.symm ∘ PresentedGroup.of := rfl
  rw [this, Set.range_comp, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure,
    PresentedGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (MulEquiv.surjective _)
theorem submonoid_closure_range_simple : Submonoid.closure (range cs.simple) = ⊤ := by
  have : range cs.simple = range cs.simple ∪ (range cs.simple)⁻¹ := by
    simp_rw [inv_range, inv_simple, union_self]
  rw [this, ← Subgroup.closure_toSubmonoid, subgroup_closure_range_simple, Subgroup.top_toSubmonoid]
theorem simple_induction {p : W → Prop} (w : W) (simple : ∀ i : B, p (s i)) (one : p 1)
    (mul : ∀ w w' : W, p w → p w' → p (w * w')) : p w := by
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  exact Submonoid.closure_induction (fun x ⟨i, hi⟩ ↦ hi ▸ simple i) one (fun _ _ _ _ ↦ mul _ _)
    this
theorem simple_induction_left {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_left : ∀ (w : W) (i : B), p w → p (s i * w)) : p w := by
  let p' : (w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_left (p := p')
  · exact one
  · rintro _ ⟨i, rfl⟩ y _
    exact mul_simple_left y i
  · exact this
theorem simple_induction_right {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_right : ∀ (w : W) (i : B), p w → p (w * s i)) : p w := by
  let p' : ((w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop) :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_right (p := p')
  · exact one
  · rintro x _ _ ⟨i, rfl⟩
    exact mul_simple_right x i
  · exact this
theorem ext_simple {G : Type*} [Monoid G] {φ₁ φ₂ : W →* G} (h : ∀ i : B, φ₁ (s i) = φ₂ (s i)) :
    φ₁ = φ₂ :=
  MonoidHom.eq_of_eqOn_denseM cs.submonoid_closure_range_simple (fun _ ⟨i, hi⟩ ↦ hi ▸ h i)
def _root_.CoxeterMatrix.IsLiftable {G : Type*} [Monoid G] (M : CoxeterMatrix B) (f : B → G) :
    Prop := ∀ i i', (f i * f i') ^ M i i' = 1
private theorem relations_liftable {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f)
    (r : FreeGroup B) (hr : r ∈ M.relationsSet) : (FreeGroup.lift f) r = 1 := by
  rcases hr with ⟨⟨i, i'⟩, rfl⟩
  rw [uncurry, relation, map_pow, _root_.map_mul, FreeGroup.lift.of, FreeGroup.lift.of]
  exact hf i i'
private def groupLift {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  (PresentedGroup.toGroup (relations_liftable hf)).comp cs.mulEquiv.toMonoidHom
private def restrictUnit {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    Gˣ where
  val := f i
  inv := f i
  val_inv := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i
  inv_val := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i
private theorem toMonoidHom_apply_symm_apply (a : PresentedGroup (M.relationsSet)) :
    (MulEquiv.toMonoidHom cs.mulEquiv : W →* PresentedGroup (M.relationsSet))
    ((MulEquiv.symm cs.mulEquiv) a) = a := calc
  _ = cs.mulEquiv ((MulEquiv.symm cs.mulEquiv) a) := by rfl
  _ = _                                           := by rw [MulEquiv.apply_symm_apply]
def lift {G : Type*} [Monoid G] : {f : B → G // IsLiftable M f} ≃ (W →* G) where
  toFun f := MonoidHom.comp (Units.coeHom G) (cs.groupLift
    (show ∀ i i', ((restrictUnit f.property) i * (restrictUnit f.property) i') ^ M i i' = 1 from
      fun i i' ↦ Units.ext (f.property i i')))
  invFun ι := ⟨ι ∘ cs.simple, fun i i' ↦ by
    rw [comp_apply, comp_apply, ← map_mul, ← map_pow, simple_mul_simple_pow, map_one]⟩
  left_inv f := by
    ext i
    simp only [MonoidHom.comp_apply, comp_apply, mem_setOf_eq, groupLift, simple]
    rw [← MonoidHom.toFun_eq_coe, toMonoidHom_apply_symm_apply, PresentedGroup.toGroup.of,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Units.coeHom_apply, restrictUnit]
  right_inv ι := by
    apply cs.ext_simple
    intro i
    dsimp only
    rw [groupLift, simple, MonoidHom.comp_apply, MonoidHom.comp_apply, toMonoidHom_apply_symm_apply,
      PresentedGroup.toGroup.of, CoxeterSystem.restrictUnit, Units.coeHom_apply]
    simp only [comp_apply, simple]
@[simp]
theorem lift_apply_simple {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    cs.lift ⟨f, hf⟩ (s i) = f i := congrFun (congrArg Subtype.val (cs.lift.left_inv ⟨f, hf⟩)) i
theorem simple_determines_coxeterSystem :
    Injective (simple : CoxeterSystem M W → B → W) := by
  intro cs1 cs2 h
  apply CoxeterSystem.ext
  apply MulEquiv.toMonoidHom_injective
  apply cs1.ext_simple
  intro i
  nth_rw 2 [h]
  simp [simple]
def wordProd (ω : List B) : W := prod (map cs.simple ω)
local prefix:100 "π" => cs.wordProd
@[simp] theorem wordProd_nil : π [] = 1 := by simp [wordProd]
theorem wordProd_cons (i : B) (ω : List B) : π (i :: ω) = s i * π ω := by simp [wordProd]
@[simp] theorem wordProd_singleton (i : B) : π ([i]) = s i := by simp [wordProd]
theorem wordProd_concat (i : B) (ω : List B) : π (ω.concat i) = π ω * s i := by simp [wordProd]
theorem wordProd_append (ω ω' : List B) : π (ω ++ ω') = π ω * π ω' := by simp [wordProd]
@[simp] theorem wordProd_reverse (ω : List B) : π (reverse ω) = (π ω)⁻¹ := by
  induction' ω with x ω' ih
  · simp
  · simpa [wordProd_cons, wordProd_append] using ih
theorem wordProd_surjective : Surjective cs.wordProd := by
  intro w
  apply cs.simple_induction_left w
  · use []
    rw [wordProd_nil]
  · rintro _ i ⟨ω, rfl⟩
    use i :: ω
    rw [wordProd_cons]
def alternatingWord (i i' : B) (m : ℕ) : List B :=
  match m with
  | 0    => []
  | m+1  => (alternatingWord i' i m).concat i'
abbrev braidWord (M : CoxeterMatrix B) (i i' : B) : List B := alternatingWord i i' (M i i')
theorem alternatingWord_succ (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (alternatingWord i' i m).concat i' := rfl
theorem alternatingWord_succ' (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternatingWord i i' m := by
  induction' m with m ih generalizing i i'
  · simp [alternatingWord]
  · rw [alternatingWord]
    nth_rw 1 [ih i' i]
    rw [alternatingWord]
    simp [Nat.even_add_one, ← Nat.not_even_iff_odd]
@[simp]
theorem length_alternatingWord (i i' : B) (m : ℕ) :
    List.length (alternatingWord i i' m) = m := by
  induction' m with m ih generalizing i i'
  · dsimp [alternatingWord]
  · simpa [alternatingWord] using ih i' i
lemma getElem_alternatingWord (i j : B) (p k : ℕ) (hk : k < p) :
    (alternatingWord i j p)[k]'(by simp; exact hk) =  (if Even (p + k) then i else j) := by
  revert k
  induction p with
  | zero =>
    intro k hk
    simp only [not_lt_zero'] at hk
  | succ n h =>
    intro k hk
    simp_rw [alternatingWord_succ' i j n]
    match k with
    | 0 =>
      by_cases h2 : Even n
      · simp only [h2, ↓reduceIte, getElem_cons_zero, add_zero,
        (by simp [Even.add_one, h2] : ¬Even (n + 1))]
      · simp only [h2, ↓reduceIte, getElem_cons_zero, add_zero,
        Odd.add_one (Nat.not_even_iff_odd.mp h2)]
    | k + 1 =>
      simp only [add_lt_add_iff_right] at hk h
      simp only [getElem_cons_succ, h k hk]
      ring_nf
      have even_add_two (m : ℕ) : Even (2 + m) ↔ Even m := by
        simp only [add_tsub_cancel_right, even_two, (Nat.even_sub (by omega : m ≤ 2 + m)).mp]
      by_cases h_even : Even (n + k)
      · rw [if_pos h_even]
        rw [← even_add_two (n+k), ← Nat.add_assoc 2 n k] at h_even
        rw [if_pos h_even]
      · rw [if_neg h_even]
        rw [← even_add_two (n+k), ← Nat.add_assoc 2 n k] at h_even
        rw [if_neg h_even]
lemma getElem_alternatingWord_swapIndices (i j : B) (p k : ℕ) (h : k + 1 < p) :
   (alternatingWord i j p)[k+1]'(by simp; exact h) =
   (alternatingWord j i p)[k]'(by simp [h]; omega) := by
  rw [getElem_alternatingWord i j p (k+1) (by omega), getElem_alternatingWord j i p k (by omega)]
  by_cases h_even : Even (p + k)
  · rw [if_pos h_even, ← add_assoc]
    simp only [ite_eq_right_iff, isEmpty_Prop, Nat.not_even_iff_odd, Even.add_one h_even,
      IsEmpty.forall_iff]
  · rw [if_neg h_even, ← add_assoc]
    simp [Odd.add_one (Nat.not_even_iff_odd.mp h_even)]
lemma listTake_alternatingWord (i j : B) (p k : ℕ) (h : k < 2 * p) :
    List.take k (alternatingWord i j (2 * p)) =
    if Even k then alternatingWord i j k else alternatingWord j i k := by
  induction k with
    | zero =>
      simp only [take_zero, even_zero, ↓reduceIte, alternatingWord]
    | succ k h' =>
      have hk : k < 2 * p := by omega
      apply h' at hk
      by_cases h_even : Even k
      · simp only [h_even, ↓reduceIte] at hk
        simp only [Nat.not_even_iff_odd.mpr (Even.add_one h_even), ↓reduceIte]
        rw [← List.take_concat_get _ _ (by simp[h]; omega), alternatingWord_succ, ← hk]
        apply congr_arg
        rw [getElem_alternatingWord i j (2*p) k (by omega)]
        simp [(by apply Nat.even_add.mpr; simp[h_even]: Even (2 * p + k))]
      · simp only [h_even, ↓reduceIte] at hk
        simp only [(by simp at h_even; exact Odd.add_one h_even : Even (k + 1)), ↓reduceIte]
        rw [← List.take_concat_get _ _ (by simp[h]; omega), alternatingWord_succ, hk]
        apply congr_arg
        rw [getElem_alternatingWord i j (2*p) k (by omega)]
        simp [(by apply Nat.odd_add.mpr; simp[h_even]: Odd (2 * p + k))]
lemma listTake_succ_alternatingWord (i j : B) (p : ℕ) (k : ℕ) (h : k + 1 < 2 * p) :
    List.take (k + 1) (alternatingWord i j (2 * p)) =
    i :: (List.take k (alternatingWord j i (2 * p))) := by
  rw [listTake_alternatingWord j i p k (by omega), listTake_alternatingWord i j p (k+1) h]
  by_cases h_even : Even k
  · simp [h_even, Nat.not_even_iff_odd.mpr (Even.add_one h_even), alternatingWord_succ', h_even]
  · simp [h_even, (by simp at h_even; exact Odd.add_one h_even: Even (k + 1)),
    alternatingWord_succ', h_even]
theorem prod_alternatingWord_eq_mul_pow (i i' : B) (m : ℕ) :
    π (alternatingWord i i' m) = (if Even m then 1 else s i') * (s i * s i') ^ (m / 2) := by
  induction' m with m ih
  · simp [alternatingWord]
  · rw [alternatingWord_succ', wordProd_cons, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]
theorem prod_alternatingWord_eq_prod_alternatingWord_sub (i i' : B) (m : ℕ) (hm : m ≤ M i i' * 2) :
    π (alternatingWord i i' m) = π (alternatingWord i' i (M i i' * 2 - m)) := by
  simp_rw [prod_alternatingWord_eq_mul_pow, ← Int.even_coe_nat]
  simp_rw [← zpow_natCast, Int.ofNat_ediv, Int.ofNat_sub hm]
  generalize (m : ℤ) = m'
  clear hm
  push_cast
  rcases Int.even_or_odd' m' with ⟨k, rfl | rfl⟩
  · rw [if_pos (by use k; ring), if_pos (by use -k + (M i i'); ring), mul_comm 2 k, ← sub_mul]
    repeat rw [Int.mul_ediv_cancel _ (by norm_num)]
    rw [zpow_sub, zpow_natCast, simple_mul_simple_pow' cs i i', ← inv_zpow]
    simp
  · have : ¬Even (2 * k + 1) := Int.not_even_iff_odd.2 ⟨k, rfl⟩
    rw [if_neg this]
    have : ¬Even (↑(M i i') * 2 - (2 * k + 1)) :=
      Int.not_even_iff_odd.2 ⟨↑(M i i') - k - 1, by ring⟩
    rw [if_neg this]
    rw [(by ring : ↑(M i i') * 2 - (2 * k + 1) = -1 + (-k + ↑(M i i')) * 2),
      (by ring : 2 * k + 1 = 1 + k * 2)]
    repeat rw [Int.add_mul_ediv_right _ _ (by norm_num)]
    norm_num
    rw [zpow_add, zpow_add, zpow_natCast, simple_mul_simple_pow', zpow_neg, ← inv_zpow, zpow_neg,
      ← inv_zpow]
    simp [← mul_assoc]
theorem wordProd_braidWord_eq (i i' : B) :
    π (braidWord M i i') = π (braidWord M i' i) := by
  have := cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' (M i i')
    (Nat.le_mul_of_pos_right _ (by norm_num))
  rw [tsub_eq_of_eq_add (mul_two (M i i'))] at this
  nth_rw 2 [M.symmetric i i'] at this
  exact this
end CoxeterSystem