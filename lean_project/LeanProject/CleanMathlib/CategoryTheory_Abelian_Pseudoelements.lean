import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Algebra.Category.ModuleCat.EpiMono
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Abelian
open CategoryTheory.Preadditive
universe v u
namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C]
attribute [local instance] Over.coeFromHom
def app {P Q : C} (f : P ⟶ Q) (a : Over P) : Over Q :=
  a.hom ≫ f
@[simp]
theorem app_hom {P Q : C} (f : P ⟶ Q) (a : Over P) : (app f a).hom = a.hom ≫ f := rfl
def PseudoEqual (P : C) (f g : Over P) : Prop :=
  ∃ (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom
theorem pseudoEqual_refl {P : C} : Reflexive (PseudoEqual P) :=
  fun f => ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩
theorem pseudoEqual_symm {P : C} : Symmetric (PseudoEqual P) :=
  fun _ _ ⟨R, p, q, ep, Eq, comm⟩ => ⟨R, q, p, Eq, ep, comm.symm⟩
variable [Abelian.{v} C]
section
theorem pseudoEqual_trans {P : C} : Transitive (PseudoEqual P) := by
  intro f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩
  refine ⟨pullback q p', pullback.fst _ _ ≫ p, pullback.snd _ _ ≫ q',
    epi_comp _ _, epi_comp _ _, ?_⟩
  rw [Category.assoc, comm, ← Category.assoc, pullback.condition, Category.assoc, comm',
    Category.assoc]
end
def Pseudoelement.setoid (P : C) : Setoid (Over P) :=
  ⟨_, ⟨pseudoEqual_refl, @pseudoEqual_symm _ _ _, @pseudoEqual_trans _ _ _ _⟩⟩
attribute [local instance] Pseudoelement.setoid
def Pseudoelement (P : C) : Type max u v :=
  Quotient (Pseudoelement.setoid P)
namespace Pseudoelement
def objectToSort : CoeSort C (Type max u v) :=
  ⟨fun P => Pseudoelement P⟩
attribute [local instance] objectToSort
scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
def overToSort {P : C} : Coe (Over P) (Pseudoelement P) :=
  ⟨Quot.mk (PseudoEqual P)⟩
attribute [local instance] overToSort
theorem over_coe_def {P Q : C} (a : Q ⟶ P) : (a : Pseudoelement P) = ⟦↑a⟧ := rfl
theorem pseudoApply_aux {P Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b → app f a ≈ app f b :=
  fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩
def pseudoApply {P Q : C} (f : P ⟶ Q) : P → Q :=
  Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)
def homToFun {P Q : C} : CoeFun (P ⟶ Q) fun _ => P → Q :=
  ⟨pseudoApply⟩
attribute [local instance] homToFun
scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.homToFun
theorem pseudoApply_mk' {P Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧ := rfl
theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
  Quotient.inductionOn a fun x =>
    Quotient.sound <| by
      simp only [app]
      rw [← Category.assoc, Over.coe_hom]
theorem comp_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : g ∘ f = f ≫ g :=
  funext fun _ => (comp_apply _ _ _).symm
section Zero
section
attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts
theorem pseudoZero_aux {P : C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0 :=
  ⟨fun ⟨R, p, q, _, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf, Over.coe_hom, HasZeroMorphisms.comp_zero, HasZeroMorphisms.comp_zero]⟩⟩
end
theorem zero_eq_zero' {P Q R : C} :
    (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) = ⟦((0 : R ⟶ P) : Over P)⟧ :=
  Quotient.sound <| (pseudoZero_aux R _).2 rfl
def pseudoZero {P : C} : P :=
  ⟦(0 : P ⟶ P)⟧
instance hasZero {P : C} : Zero P :=
  ⟨pseudoZero⟩
instance {P : C} : Inhabited P :=
  ⟨0⟩
theorem pseudoZero_def {P : C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧ := rfl
@[simp]
theorem zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P) :=
  zero_eq_zero'
theorem pseudoZero_iff {P : C} (a : Over P) : a = (0 : P) ↔ a.hom = 0 := by
  rw [← pseudoZero_aux P a]
  exact Quotient.eq'
end Zero
open Pseudoelement
@[simp]
theorem apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 := by
  rw [pseudoZero_def, pseudoApply_mk']
  simp
@[simp]
theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
  Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def, pseudoApply_mk']
    simp
theorem zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → f = 0 := fun h => by
  rw [← Category.id_comp f]
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))
theorem zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → 0 = f :=
  Eq.symm ∘ zero_morphism_ext f
theorem eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ a, f a = 0 :=
  ⟨fun h a => by simp [h], zero_morphism_ext _⟩
theorem pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [Mono f] : Function.Injective f := by
  intro abar abar'
  refine Quotient.inductionOn₂ abar abar' fun a a' ha => ?_
  apply Quotient.sound
  have : (⟦(a.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(a'.hom ≫ f)⟧ := by convert ha
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
  exact ⟨R, p, q, ep, Eq, (cancel_mono f).1 <| by
    simp only [Category.assoc]
    exact comm⟩
theorem zero_of_map_zero {P Q : C} (f : P ⟶ Q) : Function.Injective f → ∀ a, f a = 0 → a = 0 :=
  fun h a ha => by
  rw [← apply_zero f] at ha
  exact h ha
theorem mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0 → a = 0) → Mono f :=
  fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
    (pseudoZero_iff (g : Over P)).1 <|
      h _ <| show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg
section
theorem pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [Epi f] : Function.Surjective f :=
  fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨(pullback.fst f q.hom : Over P),
      Quotient.sound <|
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd _ _, inferInstance, inferInstance, by
          rw [Category.id_comp, ← pullback.condition, app_hom, Over.coe_hom]⟩⟩
end
theorem epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : Function.Surjective f → Epi f := by
  intro h
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  have : (⟦(p.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f y ey
  dsimp at comm
  rw [Category.assoc, comm]
  apply Category.comp_id
section
theorem pseudo_exact_of_exact {S : ShortComplex C} (hS : S.Exact) :
    ∀ b, S.g b = 0 → ∃ a, S.f a = b :=
  fun b' =>
    Quotient.inductionOn b' fun b hb => by
      have hb' : b.hom ≫ S.g = 0 := (pseudoZero_iff _).1 hb
      obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' hS.isLimitImage _ hb'
      use pullback.fst (Abelian.factorThruImage S.f) c
      apply Quotient.sound
      refine ⟨pullback (Abelian.factorThruImage S.f) c, 𝟙 _,
              pullback.snd _ _, inferInstance, inferInstance, ?_⟩
      calc
        𝟙 (pullback (Abelian.factorThruImage S.f) c) ≫ pullback.fst _ _ ≫ S.f =
          pullback.fst _ _ ≫ S.f :=
          Category.id_comp _
        _ = pullback.fst _ _ ≫ Abelian.factorThruImage S.f ≫ kernel.ι (cokernel.π S.f) := by
          rw [Abelian.image.fac]
        _ = (pullback.snd _ _ ≫ c) ≫ kernel.ι (cokernel.π S.f) := by
          rw [← Category.assoc, pullback.condition]
        _ = pullback.snd _ _ ≫ b.hom := by
          rw [Category.assoc]
          congr
end
theorem apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → f a = 0 :=
  fun h => by simp [over_coe_def, pseudoApply_mk', Over.coe_hom, h]
section
theorem exact_of_pseudo_exact (S : ShortComplex C)
    (hS : ∀ b, S.g b = 0 → ∃ a, S.f a = b) : S.Exact :=
  (S.exact_iff_kernel_ι_comp_cokernel_π_zero).2 (by
      have : S.g (kernel.ι S.g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _)
      obtain ⟨a', ha⟩ := hS _ this
      obtain ⟨a, ha'⟩ := Quotient.exists_rep a'
      rw [← ha'] at ha
      obtain ⟨Z, r, q, _, eq, comm⟩ := Quotient.exact ha
      obtain ⟨z, _, hz₂⟩ := @pullback.lift' _ _ _ _ _ _ (kernel.ι (cokernel.π S.f))
        (kernel.ι S.g) _ (r ≫ a.hom ≫ Abelian.factorThruImage S.f) q (by
          simp only [Category.assoc, Abelian.image.fac]
          exact comm)
      let j : pullback (kernel.ι (cokernel.π S.f)) (kernel.ι S.g) ⟶ kernel S.g := pullback.snd _ _
      haveI pe : Epi j := epi_of_epi_fac hz₂
      haveI : IsIso j := isIso_of_mono_of_epi _
      rw [(Iso.eq_inv_comp (asIso j)).2 pullback.condition.symm]
      simp only [Category.assoc, kernel.condition, HasZeroMorphisms.comp_zero])
end
theorem sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) :
    f x = f y → ∃ z, f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 → g z = g x :=
  Quotient.inductionOn₂ x y fun a a' h =>
    match Quotient.exact h with
    | ⟨R, p, q, ep, _, comm⟩ =>
      let a'' : R ⟶ P := ↑(p ≫ a.hom) - ↑(q ≫ a'.hom)
      ⟨a'',
        ⟨show ⟦(a'' ≫ f : Over Q)⟧ = ⟦↑(0 : Q ⟶ Q)⟧ by
            dsimp at comm
            simp [a'', sub_eq_zero.2 comm],
          fun Z g hh => by
          obtain ⟨X, p', q', ep', _, comm'⟩ := Quotient.exact hh
          have : a'.hom ≫ g = 0 := by
            apply (epi_iff_cancel_zero _).1 ep' _ (a'.hom ≫ g)
            simpa using comm'
          apply Quotient.sound
          change app g (a'' : Over P) ≈ app g a
          exact ⟨R, 𝟙 R, p, inferInstance, ep, by simp [a'', sub_eq_add_neg, this]⟩⟩⟩
variable [Limits.HasPullbacks C]
theorem pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} :
    f p = g q →
      ∃ s, pullback.fst f g s = p ∧ pullback.snd f g s = q :=
  Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, by rwa [Category.id_comp]⟩,
      Quotient.sound ⟨Z, 𝟙 Z, b, inferInstance, eb, by rwa [Category.id_comp]⟩⟩⟩
section Module
theorem ModuleCat.eq_range_of_pseudoequal {R : Type*} [CommRing R] {G : ModuleCat R} {x y : Over G}
    (h : PseudoEqual G x y) : LinearMap.range x.hom = LinearMap.range y.hom := by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  refine Submodule.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    refine ⟨q a'', ?_⟩
    erw [← LinearMap.comp_apply, ← ModuleCat.comp_def, ← H,
      ModuleCat.comp_def, LinearMap.comp_apply, ha'', ha']
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective q).1 hq a'
    refine ⟨p a'', ?_⟩
    erw [← LinearMap.comp_apply, ← ModuleCat.comp_def, H, ModuleCat.comp_def, LinearMap.comp_apply,
      ha'', ha']
end Module
end Pseudoelement
end CategoryTheory.Abelian