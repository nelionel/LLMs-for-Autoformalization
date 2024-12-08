import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Pi
import Mathlib.Tactic.GCongr.CoreAttrs
class OrderedSMul (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M] :
  Prop where
  protected smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b
  protected lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b
variable {ι 𝕜 R M N : Type*}
section OrderedSMul
variable [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M] [OrderedSMul R M]
instance OrderedSMul.toPosSMulStrictMono : PosSMulStrictMono R M where
  elim _a ha _b₁ _b₂ hb := OrderedSMul.smul_lt_smul_of_pos hb ha
instance OrderedSMul.toPosSMulReflectLT : PosSMulReflectLT R M :=
  PosSMulReflectLT.of_pos fun _a ha _b₁ _b₂ h ↦ OrderedSMul.lt_of_smul_lt_smul_of_pos h ha
instance OrderDual.instOrderedSMul : OrderedSMul R Mᵒᵈ where
  smul_lt_smul_of_pos := OrderedSMul.smul_lt_smul_of_pos (M := M)
  lt_of_smul_lt_smul_of_pos := OrderedSMul.lt_of_smul_lt_smul_of_pos (M := M)
end OrderedSMul
theorem OrderedSMul.mk'' [OrderedSemiring 𝕜] [LinearOrderedAddCommMonoid M] [SMulWithZero 𝕜 M]
    (h : ∀ ⦃c : 𝕜⦄, 0 < c → StrictMono fun a : M => c • a) : OrderedSMul 𝕜 M :=
  { smul_lt_smul_of_pos := fun hab hc => h hc hab
    lt_of_smul_lt_smul_of_pos := fun hab hc => (h hc).lt_iff_lt.1 hab }
instance Nat.orderedSMul [LinearOrderedCancelAddCommMonoid M] : OrderedSMul ℕ M :=
  OrderedSMul.mk'' fun n hn a b hab => by
    cases n with
    | zero => cases hn
    | succ n =>
      induction n with
      | zero => dsimp; rwa [one_nsmul, one_nsmul]
      | succ n ih => simp only [succ_nsmul _ n.succ, _root_.add_lt_add (ih n.succ_pos) hab]
instance Int.orderedSMul [LinearOrderedAddCommGroup M] : OrderedSMul ℤ M :=
  OrderedSMul.mk'' fun n hn => by
    cases n
    · simp only [Int.ofNat_eq_coe, Int.natCast_pos, natCast_zsmul] at hn ⊢
      exact strictMono_smul_left_of_pos hn
    · cases (Int.negSucc_not_pos _).1 hn
section LinearOrderedSemiring
variable [LinearOrderedSemiring R]
instance LinearOrderedSemiring.toOrderedSMul : OrderedSMul R R :=
  OrderedSMul.mk'' fun _ => strictMono_mul_left_of_pos
end LinearOrderedSemiring
section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] [OrderedAddCommMonoid M] [OrderedAddCommMonoid N]
  [MulActionWithZero 𝕜 M] [MulActionWithZero 𝕜 N]
theorem OrderedSMul.mk' (h : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a ≤ c • b) :
    OrderedSMul 𝕜 M := by
  have hlt' : ∀ (a b : M) (c : 𝕜), a < b → 0 < c → c • a < c • b := by
    refine fun a b c hab hc => (h hab hc).lt_of_ne ?_
    rw [Ne, hc.ne'.isUnit.smul_left_cancel]
    exact hab.ne
  refine ⟨fun {a b c} => hlt' a b c, fun {a b c hab hc} => ?_⟩
  obtain ⟨c, rfl⟩ := hc.ne'.isUnit
  rw [← inv_smul_smul c a, ← inv_smul_smul c b]
  refine hlt' _ _ _ hab (pos_of_mul_pos_right ?_ hc.le)
  simp only [c.mul_inv, zero_lt_one]
instance [OrderedSMul 𝕜 M] [OrderedSMul 𝕜 N] : OrderedSMul 𝕜 (M × N) :=
  OrderedSMul.mk' fun _ _ _ h hc =>
    ⟨smul_le_smul_of_nonneg_left h.1.1 hc.le, smul_le_smul_of_nonneg_left h.1.2 hc.le⟩
instance Pi.orderedSMul {M : ι → Type*} [∀ i, OrderedAddCommMonoid (M i)]
    [∀ i, MulActionWithZero 𝕜 (M i)] [∀ i, OrderedSMul 𝕜 (M i)] : OrderedSMul 𝕜 (∀ i, M i) :=
  OrderedSMul.mk' fun _ _ _ h hc i => smul_le_smul_of_nonneg_left (h.le i) hc.le
end LinearOrderedSemifield
section Invertible
variable (α : Type*) {β : Type*}
variable [Semiring α] [Invertible (2 : α)] [Lattice β] [AddCommGroup β] [Module α β]
  [AddLeftMono β]
lemma inf_eq_half_smul_add_sub_abs_sub (x y : β) : x ⊓ y = (⅟2 : α) • (x + y - |y - x|) := by
  rw [← two_nsmul_inf_eq_add_sub_abs_sub x y, two_smul, ← two_smul α,
    smul_smul, invOf_mul_self, one_smul]
lemma sup_eq_half_smul_add_add_abs_sub (x y : β) : x ⊔ y = (⅟2 : α) • (x + y + |y - x|) := by
  rw [← two_nsmul_sup_eq_add_add_abs_sub x y, two_smul, ← two_smul α,
    smul_smul, invOf_mul_self, one_smul]
end Invertible
section DivisionSemiring
variable (α : Type*) {β : Type*}
variable [DivisionSemiring α] [NeZero (2 : α)] [Lattice β] [AddCommGroup β] [Module α β]
  [AddLeftMono β]
lemma inf_eq_half_smul_add_sub_abs_sub' (x y : β) : x ⊓ y = (2⁻¹ : α) • (x + y - |y - x|) := by
  letI := invertibleOfNonzero (two_ne_zero' α)
  exact inf_eq_half_smul_add_sub_abs_sub α x y
lemma sup_eq_half_smul_add_add_abs_sub' (x y : β) : x ⊔ y = (2⁻¹ : α) • (x + y + |y - x|) := by
  letI := invertibleOfNonzero (two_ne_zero' α)
  exact sup_eq_half_smul_add_add_abs_sub α x y
end DivisionSemiring