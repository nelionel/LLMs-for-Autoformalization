import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Data.Int.Cast.Pi
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Order.Filter.Tendsto
assert_not_exists OrderedSemiring
namespace Filter
variable {α β γ δ : Type*} {l : Filter α} {f g h : α → β}
theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ _ in l, a = b) ↔ a = b :=
  eventually_const
theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b
def germSetoid (l : Filter α) (β : Type*) : Setoid (α → β) where
  r := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩
def Germ (l : Filter α) (β : Type*) : Type _ :=
  Quotient (germSetoid l β)
def productSetoid (l : Filter α) (ε : α → Type*) : Setoid ((a : _) → ε a) where
  r f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩
def Product (l : Filter α) (ε : α → Type*) : Type _ :=
  Quotient (productSetoid l ε)
namespace Product
variable {ε : α → Type*}
instance coeTC : CoeTC ((a : _) → ε a) (l.Product ε) :=
  ⟨@Quotient.mk' _ (productSetoid _ ε)⟩
instance instInhabited [(a : _) → Inhabited (ε a)] : Inhabited (l.Product ε) :=
  ⟨(↑fun a => (default : ε a) : l.Product ε)⟩
end Product
namespace Germ
@[coe]
def ofFun : (α → β) → (Germ l β) := @Quotient.mk' _ (germSetoid _ _)
instance : CoeTC (α → β) (Germ l β) :=
  ⟨ofFun⟩
@[coe] 
def const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b
instance coeTC : CoeTC β (Germ l β) :=
  ⟨const⟩
def IsConstant {l : Filter α} (P : Germ l β) : Prop :=
  P.liftOn (fun f ↦ ∃ b : β, f =ᶠ[l] (fun _ ↦ b)) <| by
    suffices ∀ f g : α → β, ∀ b : β, f =ᶠ[l] g → (f =ᶠ[l] fun _ ↦ b) → (g =ᶠ[l] fun _ ↦ b) from
      fun f g h ↦ propext ⟨fun ⟨b, hb⟩ ↦ ⟨b, this f g b h hb⟩, fun ⟨b, hb⟩ ↦ ⟨b, h.trans hb⟩⟩
    exact fun f g b hfg hf ↦ (hfg.symm).trans hf
theorem isConstant_coe {l : Filter α} {b} (h : ∀ x', f x' = b) : (↑f : Germ l β).IsConstant :=
  ⟨b, Eventually.of_forall h⟩
@[simp]
theorem isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α ↦ b : Germ l β).IsConstant := by
  use b
lemma isConstant_comp {l : Filter α} {f : α → β} {g : β → γ}
    (h : (f : Germ l β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant := by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩
@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl
@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) :
    @Quotient.mk' _ (germSetoid _ _) f = (f : Germ l β) :=
  rfl
@[elab_as_elim]
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn' f h
@[elab_as_elim]
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h
@[elab_as_elim]
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  Quotient.map' F hF
def liftOn {γ : Sort*} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF
@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl
@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''
alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq
def map (op : β → γ) : Germ l β → Germ l γ :=
  map' (op ∘ ·) fun _ _ H => H.mono fun _ H => congr_arg op H
@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl
@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  rfl
theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun _ => rfl
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Quotient.map₂ (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]
@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)
@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl
alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg
@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto
@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g :=
  rfl
@[simp, nolint simpNF]
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl
theorem Filter.Tendsto.congr_germ {f g : β → γ} {l : Filter α} {l' : Filter β} (h : f =ᶠ[l'] g)
    {φ : α → β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  EventuallyEq.germ_eq (h.comp_tendsto hφ)
lemma isConstant_comp_tendsto {lc : Filter γ} {g : γ → α}
    (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β) := by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩
lemma isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ → α}
    (hf : f.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant := by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg
@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq
@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl
@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl
@[simp]
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b :=
  rfl
@[simp]
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun _f _g H =>
    propext <| eventually_congr <| H.mono fun _x hx => hx ▸ Iff.rfl
@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl
theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  Eventually.of_forall fun _y => hx
@[simp]
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => ∀ᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl
@[simp]
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl
theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  Eventually.of_forall fun _ => h
@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)
instance instInhabited [Inhabited β] : Inhabited (Germ l β) := ⟨↑(default : β)⟩
section Monoid
variable {M : Type*} {G : Type*}
@[to_additive] instance instMul [Mul M] : Mul (Germ l M) := ⟨map₂ (· * ·)⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl
@[to_additive] instance instOne [One M] : One (Germ l M) := ⟨↑(1 : M)⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl
@[to_additive]
instance instSemigroup [Semigroup M] : Semigroup (Germ l M) :=
  { mul_assoc := fun a b c => Quotient.inductionOn₃' a b c
      fun _ _ _ => congrArg ofFun <| mul_assoc .. }
@[to_additive]
instance instCommSemigroup [CommSemigroup M] : CommSemigroup (Germ l M) :=
  { mul_comm := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_comm .. }
@[to_additive]
instance instIsLeftCancelMul [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (Germ l M) where
  mul_left_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel)
@[to_additive]
instance instIsRightCancelMul [Mul M] [IsRightCancelMul M] : IsRightCancelMul (Germ l M) where
  mul_right_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 <| (coe_eq.1 H).mono fun _x => mul_right_cancel
@[to_additive]
instance instIsCancelMul [Mul M] [IsCancelMul M] : IsCancelMul (Germ l M) where
@[to_additive]
instance instLeftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) where
  mul_left_cancel _ _ _ := mul_left_cancel
@[to_additive]
instance instRightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) where
  mul_right_cancel _ _ _ := mul_right_cancel
@[to_additive]
instance instMulOneClass [MulOneClass M] : MulOneClass (Germ l M) :=
  { one_mul := Quotient.ind' fun _ => congrArg ofFun <| one_mul _
    mul_one := Quotient.ind' fun _ => congrArg ofFun <| mul_one _ }
@[to_additive]
instance instSMul [SMul M G] : SMul M (Germ l G) where smul n := map (n • ·)
@[to_additive existing instSMul]
instance instPow [Pow G M] : Pow (Germ l G) M where pow f n := map (· ^ n) f
@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = n • (f : Germ l G) :=
  rfl
@[to_additive (attr := simp, norm_cast)]
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : Germ l G) :=
  rfl
@[to_additive (attr := simp, norm_cast)]
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n :=
  rfl
@[to_additive (attr := simp, norm_cast)]
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n :=
  rfl
@[to_additive]
instance instMonoid [Monoid M] : Monoid (Germ l M) :=
  { Function.Surjective.monoid ofFun Quot.mk_surjective (by rfl)
      (fun _ _ => by rfl) fun _ _ => by rfl with
    toSemigroup := instSemigroup
    toOne := instOne
    npow := fun n a => a ^ n }
@[to_additive "Coercion from functions to germs as an additive monoid homomorphism."]
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M where
  toFun := ofFun; map_one' := rfl; map_mul' _ _ := rfl
@[to_additive (attr := simp)]
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = ofFun :=
  rfl
@[to_additive]
instance instCommMonoid [CommMonoid M] : CommMonoid (Germ l M) :=
  { mul_comm := mul_comm }
instance instNatCast [NatCast M] : NatCast (Germ l M) where natCast n := (n : α → M)
@[simp]
theorem natCast_def [NatCast M] (n : ℕ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl
@[simp, norm_cast]
theorem const_nat [NatCast M] (n : ℕ) : ((n : M) : Germ l M) = n := rfl
@[simp, norm_cast]
theorem coe_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : α → M)) : Germ l M) = OfNat.ofNat n :=
  rfl
@[simp, norm_cast]
theorem const_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : M)) : Germ l M) = OfNat.ofNat n :=
  rfl
instance instIntCast [IntCast M] : IntCast (Germ l M) where intCast n := (n : α → M)
@[simp]
theorem intCast_def [IntCast M] (n : ℤ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl
@[deprecated (since := "2024-04-05")] alias coe_nat := natCast_def
@[deprecated (since := "2024-04-05")] alias coe_int := intCast_def
instance instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) where
  natCast_zero := congrArg ofFun <| by simp; rfl
  natCast_succ _ := congrArg ofFun <| by simp [Function.comp]; rfl
instance instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (Germ l M) :=
  { add_comm := add_comm }
@[to_additive] instance instInv [Inv G] : Inv (Germ l G) := ⟨map Inv.inv⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl
@[to_additive (attr := simp, norm_cast)]
theorem const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹ :=
  rfl
@[to_additive] instance instDiv [Div M] : Div (Germ l M) := ⟨map₂ (· / ·)⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl
@[to_additive (attr := simp, norm_cast)]
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl
@[to_additive]
instance instInvolutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G) :=
  { inv_inv := Quotient.ind' fun _ => congrArg ofFun<| inv_inv _ }
instance instHasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G) :=
  { neg_mul := Quotient.ind₂' fun _ _ => congrArg ofFun <| neg_mul ..
    mul_neg := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_neg .. }
@[to_additive]
instance instInvOneClass [InvOneClass G] : InvOneClass (Germ l G) :=
  ⟨congr_arg ofFun inv_one⟩
@[to_additive subNegMonoid]
instance instDivInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) where
  zpow z f := f ^ z
  zpow_zero' := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_zero' _
  zpow_succ' _ := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_succ' ..
  zpow_neg' _ := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_neg' ..
  div_eq_mul_inv := Quotient.ind₂' fun _ _ ↦ congrArg ofFun <| div_eq_mul_inv ..
@[to_additive]
instance instDivisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where
  inv_inv := inv_inv
  mul_inv_rev x y := inductionOn₂ x y fun _ _ ↦ congr_arg ofFun <| mul_inv_rev _ _
  inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h ↦ coe_eq.2 <| (coe_eq.1 h).mono fun _ ↦
    DivisionMonoid.inv_eq_of_mul _ _
@[to_additive]
instance instGroup [Group G] : Group (Germ l G) :=
  { inv_mul_cancel := Quotient.ind' fun _ => congrArg ofFun <| inv_mul_cancel _ }
@[to_additive]
instance instCommGroup [CommGroup G] : CommGroup (Germ l G) :=
  { mul_comm := mul_comm }
instance instAddGroupWithOne [AddGroupWithOne G] : AddGroupWithOne (Germ l G) where
  __ := instAddMonoidWithOne
  __ := instAddGroup
  intCast_ofNat _ := congrArg ofFun <| by simp
  intCast_negSucc _ := congrArg ofFun <| by simp [Function.comp_def]; rfl
end Monoid
section Ring
variable {R : Type*}
instance instNontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩
instance instMulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R) :=
  { zero_mul := Quotient.ind' fun _ => congrArg ofFun <| zero_mul _
    mul_zero := Quotient.ind' fun _ => congrArg ofFun <| mul_zero _ }
instance instMulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) where
  __ := instMulZeroClass
  __ := instMulOneClass
instance instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) where
  __ := instMonoid
  __ := instMulZeroClass
instance instDistrib [Distrib R] : Distrib (Germ l R) where
  left_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ ↦ congrArg ofFun <| left_distrib ..
  right_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ ↦ congrArg ofFun <| right_distrib ..
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Germ l R) where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R) :=
  { mul_assoc := mul_assoc }
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddMonoidWithOne
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Germ l R) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R) :=
  { mul_assoc := mul_assoc }
instance instNonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddGroupWithOne
instance instSemiring [Semiring R] : Semiring (Germ l R) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero
instance instRing [Ring R] : Ring (Germ l R) where
  __ := instSemiring
  __ := instAddCommGroup
  __ := instNonAssocRing
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] :
    NonUnitalCommSemiring (Germ l R) :=
  { mul_comm := mul_comm }
instance instCommSemiring [CommSemiring R] : CommSemiring (Germ l R) :=
  { mul_comm := mul_comm }
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R) where
  __ := instNonUnitalRing
  __ := instCommSemigroup
instance instCommRing [CommRing R] : CommRing (Germ l R) :=
  { mul_comm := mul_comm }
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := ofFun }
@[simp]
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = ofFun :=
  rfl
end Ring
section Module
variable {M N R : Type*}
@[to_additive]
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_smul' [SMul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl
@[to_additive]
instance instMulAction [Monoid M] [MulAction M β] : MulAction M (Germ l β) where
  one_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [mul_smul]
@[to_additive]
instance instMulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [mul_smul]
instance instDistribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction M (Germ l N) where
  smul_add c f g :=
    inductionOn₂ f g fun f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]
instance instDistribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  smul_add c f g :=
    inductionOn₃ c f g fun c f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]
instance instModule [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M) where
  add_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [add_smul]
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [zero_smul, coe_zero]
instance instModule' [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (Germ l R) (Germ l M) where
  add_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]
end Module
instance instLE [LE β] : LE (Germ l β) := ⟨LiftRel (· ≤ ·)⟩
theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl
@[simp]
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl
theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl
theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  liftRel_const
@[simp, norm_cast]
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  liftRel_const_iff
instance instPreorder [Preorder β] : Preorder (Germ l β) where
  le := (· ≤ ·)
  le_refl f := inductionOn f <| EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun _ _ _ => EventuallyLE.trans
instance instPartialOrder [PartialOrder β] : PartialOrder (Germ l β) where
  le_antisymm f g := inductionOn₂ f g fun _ _ h₁ h₂ ↦ (EventuallyLE.antisymm h₁ h₂).germ_eq
instance instBot [Bot β] : Bot (Germ l β) := ⟨↑(⊥ : β)⟩
instance instTop [Top β] : Top (Germ l β) := ⟨↑(⊤ : β)⟩
@[simp, norm_cast]
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl
@[simp, norm_cast]
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl
instance instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot_le f := inductionOn f fun _ => Eventually.of_forall fun _ => bot_le
instance instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  le_top f := inductionOn f fun _ => Eventually.of_forall fun _ => le_top
instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where
  __ := instOrderBot
  __ := instOrderTop
instance instSup [Max β] : Max (Germ l β) := ⟨map₂ (· ⊔ ·)⟩
instance instInf [Min β] : Min (Germ l β) := ⟨map₂ (· ⊓ ·)⟩
@[simp, norm_cast]
theorem const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  rfl
@[simp, norm_cast]
theorem const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  rfl
instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) where
  sup := max
  le_sup_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x ↦ le_sup_left
  le_sup_right f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ le_sup_right
  sup_le f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ ↦ h₂.mp <| h₁.mono fun _x ↦ sup_le
instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) where
  inf := min
  inf_le_left f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ inf_le_left
  inf_le_right f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ inf_le_right
  le_inf f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ ↦ h₂.mp <| h₁.mono fun _x ↦ le_inf
instance instLattice [Lattice β] : Lattice (Germ l β) where
  __ := instSemilatticeSup
  __ := instSemilatticeInf
instance instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where
  le_sup_inf f g h := inductionOn₃ f g h fun _f _g _h ↦ Eventually.of_forall fun _ ↦ le_sup_inf
@[to_additive]
instance instExistsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l β) where
  exists_mul_of_le {x y} := inductionOn₂ x y fun f g (h : f ≤ᶠ[l] g) ↦ by
    classical
    choose c hc using fun x (hx : f x ≤ g x) ↦ exists_mul_of_le hx
    refine ⟨ofFun fun x ↦ if hx : f x ≤ g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx, hc]
end Germ
end Filter