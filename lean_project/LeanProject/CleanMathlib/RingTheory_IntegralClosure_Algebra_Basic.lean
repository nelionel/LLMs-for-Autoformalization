import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
open Polynomial Submodule
section
variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)
theorem Subalgebra.isIntegral_iff (S : Subalgebra R A) :
    Algebra.IsIntegral R S ↔ ∀ x ∈ S, IsIntegral R x :=
  Algebra.isIntegral_def.trans <| .trans
    (forall_congr' fun _ ↦ (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall
section
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
theorem Algebra.IsIntegral.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsIntegral R B] : Algebra.IsIntegral R A :=
  ⟨fun _ ↦ (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩
theorem AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algebra.IsIntegral R A ↔ Algebra.IsIntegral R B :=
  ⟨fun h ↦ h.of_injective e.symm e.symm.injective, fun h ↦ h.of_injective e e.injective⟩
end
instance Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Algebra.IsIntegral R (Module.End R M) :=
  ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩
variable (R) in
theorem IsIntegral.of_finite [Module.Finite R B] (x : B) : IsIntegral R x :=
  (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)
theorem isIntegral_of_noetherian (_ : IsNoetherian R B) (x : B) : IsIntegral R x :=
  .of_finite R x
variable (R B) in
instance Algebra.IsIntegral.of_finite [Module.Finite R B] : Algebra.IsIntegral R B :=
  ⟨.of_finite R⟩
theorem IsIntegral.of_mem_of_fg (S : Subalgebra R B)
    (HS : S.toSubmodule.FG) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  have : Module.Finite R S := ⟨(fg_top _).mpr HS⟩
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))
theorem isIntegral_of_submodule_noetherian (S : Subalgebra R B)
    (H : IsNoetherian R (Subalgebra.toSubmodule S)) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  .of_mem_of_fg _ ((fg_top _).mp <| H.noetherian _) _ hx
theorem isIntegral_of_smul_mem_submodule {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [NoZeroSMulDivisors A M] (N : Submodule R M) (hN : N ≠ ⊥) (hN' : N.FG)
    (x : A) (hx : ∀ n ∈ N, x • n ∈ N) : IsIntegral R x := by
  let A' : Subalgebra R A :=
    { carrier := { x | ∀ n ∈ N, x • n ∈ N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' →ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribMulAction.toLinearMap R M x).restrict x.prop
        map_add' := by intros x y; ext; exact add_smul _ _ _
        map_smul' := by intros r s; ext; apply smul_assoc }
      (by ext; apply one_smul)
      (by intros x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ N, a ≠ (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    show Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_right ha₂)
  show IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective, ← isIntegral_algHom_iff f this]
  haveI : Module.Finite R N := by rwa [Module.finite_def, Submodule.fg_top]
  apply Algebra.IsIntegral.isIntegral
variable {f}
theorem RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral :=
  letI := f.toAlgebra
  fun _ ↦ IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial
alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral
variable (f)
theorem RingHom.IsIntegralElem.of_mem_closure {x y z : S} (hx : f.IsIntegralElem x)
    (hy : f.IsIntegralElem y) (hz : z ∈ Subring.closure ({x, y} : Set S)) : f.IsIntegralElem z := by
  letI : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule, Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)
nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z ∈ Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz
variable (f : R →+* B)
theorem RingHom.IsIntegralElem.add (f : R →+* S) {x y : S}
    (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x + y) :=
  hx.of_mem_closure f hy <|
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))
nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy
variable (f : R →+* S)
theorem RingHom.IsIntegralElem.neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegralElem (-x) :=
  hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))
theorem RingHom.IsIntegralElem.of_neg {x : S} (h : f.IsIntegralElem (-x)) : f.IsIntegralElem x :=
  neg_neg x ▸ h.neg
@[simp]
theorem RingHom.IsIntegralElem.neg_iff {x : S} : f.IsIntegralElem (-x) ↔ f.IsIntegralElem x :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩
theorem IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)
theorem IsIntegral.of_neg {x : B} (hx : IsIntegral R (-x)) : IsIntegral R x :=
  neg_neg x ▸ hx.neg
@[simp]
theorem IsIntegral.neg_iff {x : B} : IsIntegral R (-x) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_neg, IsIntegral.neg⟩
theorem RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)
nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy
theorem RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x * y) :=
  hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))
nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy
theorem IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra R S]
    [IsScalarTower R S B] {x : B} (r : R)(hx : IsIntegral S x) : IsIntegral S (r • x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ <| by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl
variable (R A)
def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap
end
theorem mem_integralClosure_iff (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    a ∈ integralClosure R A ↔ IsIntegral R a :=
  Iff.rfl