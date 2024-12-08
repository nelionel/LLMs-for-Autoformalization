import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Algebra.Group.ZeroOne
import Mathlib.Algebra.Group.Operations
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Simps.Basic
import Batteries.Logic
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
assert_not_exists Function.Injective.eq_iff
universe u v w
open Function
variable {G : Type*}
section Mul
variable [Mul G]
@[to_additive "`leftAdd g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G ↦ fun x : G ↦ g * x
@[to_additive "`rightAdd g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G ↦ fun x : G ↦ x * g
class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
attribute [to_additive IsLeftCancelAdd] IsLeftCancelMul
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
attribute [to_additive IsRightCancelAdd] IsRightCancelMul
class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop
attribute [to_additive IsCancelAdd] IsCancelMul
section IsLeftCancelMul
variable [IsLeftCancelMul G] {a b c : G}
@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c
@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩
end IsLeftCancelMul
section IsRightCancelMul
variable [IsRightCancelMul G] {a b c : G}
@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  IsRightCancelMul.mul_right_cancel a b c
@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩
end IsRightCancelMul
end Mul
@[ext]
class Semigroup (G : Type u) extends Mul G where
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
attribute [to_additive] Semigroup
section Semigroup
variable [Semigroup G]
@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc
end Semigroup
@[ext]
class AddCommMagma (G : Type u) extends Add G where
  protected add_comm : ∀ a b : G, a + b = b + a
@[ext]
class CommMagma (G : Type u) extends Mul G where
  protected mul_comm : ∀ a b : G, a * b = b * a
attribute [to_additive] CommMagma
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where
attribute [to_additive] CommSemigroup
attribute [to_additive existing] CommSemigroup.toCommMagma
section CommMagma
variable [CommMagma G]
@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`."]
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`."]
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`."]
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`."]
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }
end CommMagma
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
library_note "lower cancel priority" 
attribute [instance 75] LeftCancelSemigroup.toSemigroup 
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup 
attribute [to_additive] LeftCancelSemigroup
@[to_additive AddLeftCancelSemigroup.toIsLeftCancelAdd "Any `AddLeftCancelSemigroup` satisfies
`IsLeftCancelAdd`."]
instance (priority := 100) LeftCancelSemigroup.toIsLeftCancelMul (G : Type u)
    [LeftCancelSemigroup G] : IsLeftCancelMul G :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel }
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
attribute [instance 75] RightCancelSemigroup.toSemigroup 
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup 
attribute [to_additive] RightCancelSemigroup
@[to_additive AddRightCancelSemigroup.toIsRightCancelAdd "Any `AddRightCancelSemigroup` satisfies
`IsRightCancelAdd`."]
instance (priority := 100) RightCancelSemigroup.toIsRightCancelMul (G : Type u)
    [RightCancelSemigroup G] : IsRightCancelMul G :=
  { mul_right_cancel := RightCancelSemigroup.mul_right_cancel }
class MulOneClass (M : Type u) extends One M, Mul M where
  protected one_mul : ∀ a : M, 1 * a = a
  protected mul_one : ∀ a : M, a * 1 = a
class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a
attribute [to_additive] MulOneClass
@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨⟨one₁⟩, ⟨mul₁⟩, one_mul₁, mul_one₁⟩ @⟨⟨one₂⟩, ⟨mul₂⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)
section MulOneClass
variable {M : Type u} [MulOneClass M]
@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul
@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one
end MulOneClass
section
variable {M : Type u}
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a
attribute [to_additive existing] npowRec
variable [One M] [Semigroup M] (m n : ℕ) (hn : n ≠ 0) (a : M) (ha : 1 * a = a)
include hn ha
@[to_additive] theorem npowRec_add : npowRec (m + n) a = npowRec m a * npowRec n a := by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [Nat.zero_add, npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]
@[to_additive] theorem npowRec_succ : npowRec (n + 1) a = a * npowRec n a := by
  rw [Nat.add_comm, npowRec_add 1 n hn a ha, npowRec, npowRec, ha]
end
library_note "forgetful inheritance"
@[to_additive "Scalar multiplication by repeated self-addition,
the additive version of exponentation by repeated squaring."]
def npowBinRec {M : Type*} [One M] [Mul M] (k : ℕ) : M → M :=
  npowBinRec.go k 1
where
  @[to_additive nsmulBinRec.go "Auxiliary tail-recursive implementation for `nsmulBinRec`."]
  go (k : ℕ) : M → M → M :=
    k.binaryRec (fun y _ ↦ y) fun bn _n fn y x ↦ fn (cond bn (y * x) y) (x * x)
def npowRec' {M : Type*} [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | 1, m => m
  | k + 2, m => npowRec' (k + 1) m * m
def nsmulRec' {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | 1, m => m
  | k + 2, m => nsmulRec' (k + 1) m + m
attribute [to_additive existing] npowRec'
@[to_additive]
theorem npowRec'_succ {M : Type*} [Semigroup M] [One M] {k : ℕ} (_ : k ≠ 0) (m : M) :
    npowRec' (k + 1) m = npowRec' k m * m :=
  match k with
  | _ + 1 => rfl
@[to_additive]
theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ← ih]
@[to_additive]
theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : ℕ} (k0 : k ≠ 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec', mul_assoc]
    | k + 2 => simp [npowRec', ← mul_assoc, ih]
@[to_additive]
theorem npowRec_eq {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec (k + 1) m = 1 * npowRec' (k + 1) m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec, npowRec'_succ k.succ_ne_zero, ← mul_assoc]
      congr
      simp [ih]
@[to_additive]
theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : ℕ) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' ≠ 0 := by omega
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | z₀ => simp at hk
  | z₁ => simp [npowRec']
  | f b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, ← Nat.two_mul, npowRec'_two_mul]
    rw [npowRec'_succ (by omega), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by omega), mul_assoc]
@[to_additive
"An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled
code as an automatic parameter."]
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowRec k m
@[to_additive
"An abbreviation for `nsmulBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation
as an automatic parameter."]
abbrev npowBinRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowBinRec k m
@[to_additive (attr := csimp)]
theorem npowRec_eq_npowBinRec : @npowRecAuto = @npowBinRecAuto := by
  funext M _ _ k m
  rw [npowBinRecAuto, npowRecAuto, npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : ℕ → M → M
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl
attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZeroClass.toAdd
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  protected npow : ℕ → M → M := npowRecAuto
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl
attribute [to_additive existing] Monoid.toMulOneClass
@[default_instance high] instance Monoid.toNatPow {M : Type*} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩
instance AddMonoid.toNatSMul {M : Type*} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩
attribute [to_additive existing toNatSMul] Monoid.toNatPow
section Monoid
variable {M : Type*} [Monoid M] {a b c : M}
@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl
@[to_additive] lemma left_inv_eq_right_inv (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _
@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  Monoid.npow_succ n a
@[to_additive (attr := simp) one_nsmul]
lemma pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]
@[to_additive succ_nsmul'] lemma pow_succ' (a : M) : ∀ n, a ^ (n + 1) = a * a ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ _ n, pow_succ, pow_succ', mul_assoc]
@[to_additive]
lemma pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n := by rw [← pow_succ, pow_succ']
@[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]
@[to_additive existing two_nsmul] alias sq := pow_two
@[to_additive three'_nsmul]
lemma pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]
@[to_additive three_nsmul]
lemma pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ', pow_two]
@[to_additive nsmul_zero, simp] lemma one_pow : ∀ n, (1 : M) ^ n = 1
  | 0 => pow_zero _
  | n + 1 => by rw [pow_succ, one_pow, one_mul]
@[to_additive add_nsmul]
lemma pow_add (a : M) (m : ℕ) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, pow_zero, mul_one]
  | n + 1 => by rw [pow_succ, ← mul_assoc, ← pow_add, ← pow_succ, Nat.add_assoc]
@[to_additive] lemma pow_mul_comm (a : M) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, Nat.add_comm]
@[to_additive mul_nsmul] lemma pow_mul (a : M) (m : ℕ) : ∀ n, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero, pow_zero, pow_zero]
  | n + 1 => by rw [Nat.mul_succ, pow_add, pow_succ, pow_mul]
@[to_additive mul_nsmul']
lemma pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]
@[to_additive nsmul_left_comm]
lemma pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
end Monoid
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
attribute [to_additive existing] CommMonoid.toCommSemigroup
section LeftCancelMonoid
class AddLeftCancelMonoid (M : Type u) extends AddMonoid M, AddLeftCancelSemigroup M
attribute [instance 75] AddLeftCancelMonoid.toAddMonoid 
@[to_additive]
class LeftCancelMonoid (M : Type u) extends Monoid M, LeftCancelSemigroup M
attribute [instance 75] LeftCancelMonoid.toMonoid 
attribute [to_additive existing] LeftCancelMonoid.toLeftCancelSemigroup
end LeftCancelMonoid
section RightCancelMonoid
class AddRightCancelMonoid (M : Type u) extends AddMonoid M, AddRightCancelSemigroup M
attribute [instance 75] AddRightCancelMonoid.toAddMonoid 
@[to_additive]
class RightCancelMonoid (M : Type u) extends Monoid M, RightCancelSemigroup M
attribute [instance 75] RightCancelMonoid.toMonoid 
attribute [to_additive existing] RightCancelMonoid.toRightCancelSemigroup
end RightCancelMonoid
section CancelMonoid
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M
attribute [to_additive existing] CancelMonoid.toRightCancelMonoid
class AddCancelCommMonoid (M : Type u) extends AddCommMonoid M, AddLeftCancelMonoid M
attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid 
@[to_additive]
class CancelCommMonoid (M : Type u) extends CommMonoid M, LeftCancelMonoid M
attribute [instance 75] CancelCommMonoid.toCommMonoid 
attribute [to_additive existing] CancelCommMonoid.toLeftCancelMonoid
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }
@[to_additive toIsCancelAdd "Any `AddCancelMonoid G` satisfies `IsCancelAdd G`."]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel
    mul_right_cancel := RightCancelSemigroup.mul_right_cancel }
end CancelMonoid
def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : ℤ → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹
def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : ℕ → G → G := nsmulRec) : ℤ → G → G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a
attribute [to_additive existing] zpowRec
section InvolutiveInv
class InvolutiveNeg (A : Type*) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x
@[to_additive]
class InvolutiveInv (G : Type*) extends Inv G where
  protected inv_inv : ∀ x : G, x⁻¹⁻¹ = x
variable [InvolutiveInv G]
@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _
end InvolutiveInv
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  protected zpow : ℤ → G → G := zpowRec npowRec
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b
attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul n.succ a = zsmul n a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl
attribute [to_additive SubNegMonoid] DivInvMonoid
instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩
instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩
attribute [to_additive existing SubNegMonoid.SMulInt] DivInvMonoid.Pow
class IsAddCyclic (G : Type u) [SMul ℤ G] : Prop where
  protected exists_zsmul_surjective : ∃ g : G, Function.Surjective (· • g : ℤ → G)
@[to_additive]
class IsCyclic (G : Type u) [Pow G ℤ] : Prop where
  protected exists_zpow_surjective : ∃ g : G, Function.Surjective (g ^ · : ℤ → G)
@[to_additive]
theorem exists_zpow_surjective (G : Type*) [Pow G ℤ] [IsCyclic G] :
    ∃ g : G, Function.Surjective (g ^ · : ℤ → G) :=
  IsCyclic.exists_zpow_surjective
section DivInvMonoid
variable [DivInvMonoid G]
@[to_additive (attr := simp) zsmul_eq_smul] theorem zpow_eq_pow (n : ℤ) (x : G) :
    DivInvMonoid.zpow n x = x ^ n :=
  rfl
@[to_additive (attr := simp) zero_zsmul] theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a
@[to_additive (attr := simp, norm_cast) natCast_zsmul]
theorem zpow_natCast (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a ^ (n : ℤ) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm
@[deprecated (since := "2024-03-20")] alias zpow_coe_nat := zpow_natCast
@[deprecated (since := "2024-03-20")] alias coe_nat_zsmul := natCast_zsmul
@[to_additive ofNat_zsmul]
lemma zpow_ofNat (a : G) (n : ℕ) : a ^ (no_index (OfNat.ofNat n) : ℤ) = a ^ OfNat.ofNat n :=
  zpow_natCast ..
theorem zpow_negSucc (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a
theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : ℕ) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a
attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc
@[to_additive "Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _
alias division_def := div_eq_mul_inv
@[to_additive (attr := simp) one_zsmul]
lemma zpow_one (a : G) : a ^ (1 : ℤ) = a := by rw [zpow_ofNat, pow_one]
@[to_additive two_zsmul] lemma zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by rw [zpow_ofNat, pow_two]
@[to_additive neg_one_zsmul]
lemma zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ :=
  (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)
@[to_additive]
lemma zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ (-(n : ℤ)) = (a ^ n)⁻¹
  | _ + 1, _ => zpow_negSucc _ _
end DivInvMonoid
section InvOneClass
class NegZeroClass (G : Type*) extends Zero G, Neg G where
  protected neg_zero : -(0 : G) = 0
class SubNegZeroMonoid (G : Type*) extends SubNegMonoid G, NegZeroClass G
@[to_additive]
class InvOneClass (G : Type*) extends One G, Inv G where
  protected inv_one : (1 : G)⁻¹ = 1
@[to_additive]
class DivInvOneMonoid (G : Type*) extends DivInvMonoid G, InvOneClass G
attribute [to_additive existing] DivInvOneMonoid.toInvOneClass
variable [InvOneClass G]
@[to_additive (attr := simp)]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one
end InvOneClass
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_add_rev (a b : G) : -(a + b) = -b + -a
  protected neg_eq_of_add (a b : G) : a + b = 0 → -a = b
@[to_additive]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  protected mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  protected inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b
attribute [to_additive existing] DivisionMonoid.toInvolutiveInv
section DivisionMonoid
variable [DivisionMonoid G] {a b : G}
@[to_additive (attr := simp) neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _
@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _
@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm
end DivisionMonoid
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G
@[to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G
attribute [to_additive existing] DivisionCommMonoid.toCommMonoid
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0
attribute [to_additive] Group
section Group
variable [Group G] {a b : G}
@[to_additive (attr := simp)]
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a
@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h
@[to_additive (attr := simp)]
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]
@[deprecated (since := "2024-08-12")] alias mul_left_inv := inv_mul_cancel
@[deprecated (since := "2024-08-12")] alias mul_right_inv := mul_inv_cancel
@[deprecated (since := "2024-08-12")] alias add_left_neg := neg_add_cancel
@[deprecated (since := "2024-08-12")] alias add_right_neg := add_neg_cancel
@[deprecated (since := "2024-08-12")] alias inv_mul_self := inv_mul_cancel
@[deprecated (since := "2024-08-12")] alias mul_inv_self := mul_inv_cancel
@[deprecated (since := "2024-08-12")] alias neg_add_self := neg_add_cancel
@[deprecated (since := "2024-08-12")] alias add_right_self := add_neg_cancel
@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]
@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]
@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]
@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]
@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (inv_mul_cancel a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h ↦ by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h ↦ by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }
end Group
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G
attribute [to_additive existing] CommGroup.toCommMonoid
section CommGroup
variable [CommGroup G]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }
@[to_additive (attr := simp)] lemma inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm, mul_inv_cancel_left]
@[to_additive (attr := simp)]
lemma mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]
@[to_additive (attr := simp)] lemma inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [mul_comm, mul_inv_cancel_right]
@[to_additive (attr := simp)] lemma mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_comm, inv_mul_cancel_right]
end CommGroup
initialize_simps_projections Semigroup
initialize_simps_projections AddSemigroup
initialize_simps_projections CommSemigroup
initialize_simps_projections AddCommSemigroup
initialize_simps_projections LeftCancelSemigroup
initialize_simps_projections AddLeftCancelSemigroup
initialize_simps_projections RightCancelSemigroup
initialize_simps_projections AddRightCancelSemigroup
initialize_simps_projections Monoid
initialize_simps_projections AddMonoid
initialize_simps_projections CommMonoid
initialize_simps_projections AddCommMonoid
initialize_simps_projections LeftCancelMonoid
initialize_simps_projections AddLeftCancelMonoid
initialize_simps_projections RightCancelMonoid
initialize_simps_projections AddRightCancelMonoid
initialize_simps_projections CancelMonoid
initialize_simps_projections AddCancelMonoid
initialize_simps_projections CancelCommMonoid
initialize_simps_projections AddCancelCommMonoid
initialize_simps_projections DivInvMonoid
initialize_simps_projections SubNegMonoid
initialize_simps_projections DivInvOneMonoid
initialize_simps_projections SubNegZeroMonoid
initialize_simps_projections DivisionMonoid
initialize_simps_projections SubtractionMonoid
initialize_simps_projections DivisionCommMonoid
initialize_simps_projections SubtractionCommMonoid
initialize_simps_projections Group
initialize_simps_projections AddGroup
initialize_simps_projections CommGroup
initialize_simps_projections AddCommGroup