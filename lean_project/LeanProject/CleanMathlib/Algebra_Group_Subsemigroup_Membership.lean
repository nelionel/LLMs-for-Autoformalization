import Mathlib.Algebra.Group.Subsemigroup.Basic
assert_not_exists MonoidWithZero
variable {ι : Sort*} {M : Type*}
section NonAssoc
variable [Mul M]
open Set
namespace Subsemigroup
@[to_additive]
theorem mem_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) {x : M} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx ↦ closure_induction (fun y hy ↦ mem_iUnion.mp hy) ?_ hx
  rintro x y - - ⟨i, hi⟩ ⟨j, hj⟩
  rcases hS i j with ⟨k, hki, hkj⟩
  exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
@[to_additive]
theorem coe_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
@[to_additive]
theorem mem_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
@[to_additive]
theorem coe_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) :
    (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directed_on hS]
@[to_additive]
theorem mem_sup_left {S T : Subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  tauto
@[to_additive]
theorem mem_sup_right {S T : Subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  tauto
@[to_additive]
theorem mul_mem_sup {S T : Subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
@[to_additive]
theorem mem_iSup_of_mem {S : ι → Subsemigroup M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  have : S i ≤ iSup S := le_iSup _ _
  tauto
@[to_additive]
theorem mem_sSup_of_mem {S : Set (Subsemigroup M)} {s : Subsemigroup M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have : s ≤ sSup S := le_sSup hs
  tauto
@[to_additive (attr := elab_as_elim)
"An induction principle for elements of `⨆ i, S i`. If `C` holds all
elements of `S i` for all `i`, and is preserved under addition, then it holds for all elements of
the supremum of `S`."]
theorem iSup_induction (S : ι → Subsemigroup M) {C : M → Prop} {x₁ : M} (hx₁ : x₁ ∈ ⨆ i, S i)
    (mem : ∀ i, ∀ x₂ ∈ S i, C x₂) (mul : ∀ x y, C x → C y → C (x * y)) : C x₁ := by
  rw [iSup_eq_closure] at hx₁
  refine closure_induction (fun x₂ hx₂ => ?_) (fun x y _ _ ↦ mul x y) hx₁
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx₂
  exact mem _ _ hi
@[to_additive (attr := elab_as_elim)
"A dependent version of `AddSubsemigroup.iSup_induction`."]
theorem iSup_induction' (S : ι → Subsemigroup M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i) (x) (hxS : x ∈ S i), C x (mem_iSup_of_mem i ‹_›))
    (mul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x₁ : M}
    (hx₁ : x₁ ∈ ⨆ i, S i) : C x₁ hx₁ := by
  refine Exists.elim ?_ fun (hx₁' : x₁ ∈ ⨆ i, S i) (hc : C x₁ hx₁') => hc
  refine @iSup_induction _ _ _ S (fun x' => ∃ hx'', C x' hx'') _ hx₁
      (fun i x₂ hx₂ => ?_) fun x₃ y => ?_
  · exact ⟨_, mem _ _ hx₂⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, mul _ _ _ _ Cx Cy⟩
end Subsemigroup
end NonAssoc