import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Defs
universe u v w
namespace Ideal
open Set
variable {R : Type u} [CommRing R] (I : Ideal R) {a b : R}
variable {S : Type v}
@[instance] abbrev instHasQuotient : HasQuotient R (Ideal R) :=
  Submodule.hasQuotient
namespace Quotient
variable {I} {x y : R}
instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩
protected def ringCon (I : Ideal R) : RingCon R :=
  { QuotientAddGroup.con I.toAddSubgroup with
    mul' := fun {a₁ b₁ a₂ b₂} h₁ h₂ => by
      rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
      have F := I.add_mem (I.mul_mem_left a₂ h₁) (I.mul_mem_right b₁ h₂)
      have : a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ := by
        rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁]
      rwa [← this] at F }
instance commRing (I : Ideal R) : CommRing (R ⧸ I) where
  __ : AddCommGroup (R ⧸ I) := inferInstance
  __ : CommRing (Quotient.ringCon I).Quotient := inferInstance
example : (commRing I).toAddCommGroup = Submodule.Quotient.addCommGroup I := rfl
def mk (I : Ideal R) : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
instance {I : Ideal R} : Coe R (R ⧸ I) :=
  ⟨Ideal.Quotient.mk I⟩
@[ext 1100]
theorem ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I →+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
    f = g :=
  RingHom.ext fun x => Quotient.inductionOn' x <| (RingHom.congr_fun h : _)
instance inhabited : Inhabited (R ⧸ I) :=
  ⟨mk I 37⟩
protected theorem eq : mk I x = mk I y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I
@[simp]
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl
theorem eq_zero_iff_mem {I : Ideal R} : mk I a = 0 ↔ a ∈ I :=
  Submodule.Quotient.mk_eq_zero _
theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y ∈ I := by
  rw [← eq_zero_iff_mem, map_sub, sub_eq_zero]
theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl
instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩
theorem quotient_ring_saturate (I : Ideal R) (s : Set R) :
    mk I ⁻¹' (mk I '' s) = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩
variable [Semiring S]
def lift (I : Ideal R) (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }
@[simp]
theorem lift_mk (I : Ideal R) (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    lift I f H (mk I a) = f a :=
  rfl
theorem lift_surjective_of_surjective (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]
def factor (S T : Ideal R) (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)
@[simp]
theorem factor_mk (S T : Ideal R) (H : S ≤ T) (x : R) : factor S T H (mk S x) = mk T x :=
  rfl
@[simp]
theorem factor_comp_mk (S T : Ideal R) (H : S ≤ T) : (factor S T H).comp (mk S) = mk T := by
  ext x
  rw [RingHom.comp_apply, factor_mk]
end Quotient
def quotEquivOfEq {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }
@[simp]
theorem quotEquivOfEq_mk {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) (x : R) :
    quotEquivOfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl
@[simp]
theorem quotEquivOfEq_symm {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    (Ideal.quotEquivOfEq h).symm = Ideal.quotEquivOfEq h.symm := by ext; rfl
end Ideal