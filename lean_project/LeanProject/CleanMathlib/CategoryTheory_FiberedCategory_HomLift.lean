import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.CommSq
universe u₁ v₁ u₂ v₂
open CategoryTheory Category
variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)
namespace CategoryTheory
inductive IsHomLiftAux : ∀ {R S : 𝒮} {a b : 𝒳} (_ : R ⟶ S) (_ : a ⟶ b), Prop
  | map {a b : 𝒳} (φ : a ⟶ b) : IsHomLiftAux (p.map φ) φ
class Functor.IsHomLift {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  cond : IsHomLiftAux p f φ
macro "subst_hom_lift" p:term:max f:term:max φ:term:max : tactic =>
  `(tactic| obtain ⟨⟩ := Functor.IsHomLift.cond (p := $p) (f := $f) (φ := $φ))
@[simp]
instance {a b : 𝒳} (φ : a ⟶ b) : p.IsHomLift (p.map φ) φ where
  cond := by constructor
@[simp]
instance (a : 𝒳) : p.IsHomLift (𝟙 (p.obj a)) (𝟙 a) := by
  rw [← p.map_id]; infer_instance
namespace IsHomLift
protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : p.IsHomLift (𝟙 R) (𝟙 a) := by
  cases ha; infer_instance
section
variable {R S : 𝒮} {a b : 𝒳}
lemma domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj a = R := by
  subst_hom_lift p f φ; rfl
lemma codomain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj b = S := by
  subst_hom_lift p f φ; rfl
variable (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
lemma fac : f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ) := by
  subst_hom_lift p f φ; simp
lemma fac' : p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm := by
  subst_hom_lift p f φ; simp
lemma commSq : CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  w := by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]
end
lemma eq_of_isHomLift {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ] :
    f = p.map φ := by
  simp only [fac p f φ, eqToHom_refl, comp_id, id_comp]
lemma of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : f = eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) : p.IsHomLift f φ := by
  subst ha hb h; simp
lemma of_fac' {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance
lemma of_commsq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ ≫ eqToHom hb = (eqToHom ha) ≫ f) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance
lemma of_commSq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f) : p.IsHomLift f φ :=
  of_commsq p f φ ha hb h.1
instance comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (ψ : b ⟶ c) [p.IsHomLift f φ] [p.IsHomLift g ψ] : p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  apply of_commSq
  on_goal 1 => rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)
instance lift_id_comp (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [p.IsHomLift (𝟙 R) φ] [p.IsHomLift (𝟙 R) ψ] : p.IsHomLift (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ comp p (𝟙 R) (𝟙 R) φ ψ
instance comp_lift_id_right {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomLift f φ]
    (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using inferInstanceAs (p.IsHomLift (f ≫ 𝟙 T) (φ ≫ ψ))
lemma comp_lift_id_right' {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (T : 𝒮) (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  infer_instance
instance comp_lift_id_left {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ]
    (φ : a ⟶ b) [p.IsHomLift (𝟙 S) φ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using inferInstanceAs (p.IsHomLift (𝟙 S ≫ f) (φ ≫ ψ))
lemma comp_lift_id_left' {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ]
    {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  infer_instance
lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R) :
    p.IsHomLift (𝟙 R) (eqToHom hab) := by
  subst hR hab; simp
lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S) :
    p.IsHomLift (𝟙 S) (eqToHom hab) := by
  subst hS hab; simp
lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R) :
    p.IsHomLift (eqToHom hRS) (𝟙 a) := by
  subst hRS ha; simp
lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S) :
    p.IsHomLift (eqToHom hRS) (𝟙 b) := by
  subst hRS hb; simp
instance comp_eqToHom_lift {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a)
    [p.IsHomLift f φ] : p.IsHomLift f (eqToHom h ≫ φ) := by
  subst h; simp_all
instance eqToHom_comp_lift {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b')
    [p.IsHomLift f φ] : p.IsHomLift f (φ ≫ eqToHom h) := by
  subst h; simp_all
instance lift_eqToHom_comp {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R)
    [p.IsHomLift f φ] : p.IsHomLift (eqToHom h ≫ f) φ := by
  subst h; simp_all
instance lift_comp_eqToHom {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S')
    [p.IsHomLift f φ] : p.IsHomLift (f ≫ eqToHom h) φ := by
  subst h; simp_all
@[simp]
lemma comp_eqToHom_lift_iff {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a) :
    p.IsHomLift f (eqToHom h ≫ φ) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance
@[simp]
lemma eqToHom_comp_lift_iff {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b') :
    p.IsHomLift f (φ ≫ eqToHom h) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance
@[simp]
lemma lift_eqToHom_comp_iff {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R) :
    p.IsHomLift (eqToHom h ≫ f) φ ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance
@[simp]
lemma lift_comp_eqToHom_iff {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S') :
    p.IsHomLift (f ≫ eqToHom h) φ ↔ p.IsHomLift f φ where
  mp := fun hφ' => by subst h; simpa using hφ'
  mpr := fun _ => inferInstance
section
variable {R S : 𝒮} {a b : 𝒳}
@[simps hom]
def isoOfIsoLift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    R ≅ S where
  hom := f
  inv := eqToHom (codomain_eq p f φ.hom).symm ≫ (p.mapIso φ).inv ≫ eqToHom (domain_eq p f φ.hom)
  hom_inv_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
  inv_hom_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
@[simp]
lemma isoOfIsoLift_inv_hom_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    (isoOfIsoLift p f φ).inv ≫ f = 𝟙 S :=
  (isoOfIsoLift p f φ).inv_hom_id
@[simp]
lemma isoOfIsoLift_hom_inv_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    f ≫ (isoOfIsoLift p f φ).inv = 𝟙 R :=
  (isoOfIsoLift p f φ).hom_inv_id
lemma isIso_of_lift_isIso (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ] : IsIso f :=
  (fac p f φ) ▸ inferInstance
instance inv_lift_inv (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom] :
    p.IsHomLift f.inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (commSq p f.hom φ.hom)
instance inv_lift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    p.IsHomLift (isoOfIsoLift p f φ).inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (by apply commSq p f φ.hom)
protected instance inv (f : R ⟶ S) (φ : a ⟶ b) [IsIso f] [IsIso φ] [p.IsHomLift f φ] :
    p.IsHomLift (inv f) (inv φ) :=
  have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp_all
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)
end
instance lift_id_inv (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom] :
    p.IsHomLift (𝟙 S) φ.inv :=
  have : p.IsHomLift (asIso (𝟙 S)).hom φ.hom := by simp_all
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv_lift_inv p (asIso (𝟙 S)) φ)
instance lift_id_inv_isIso (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 S) φ] :
    p.IsHomLift (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv p _ φ)
end IsHomLift
end CategoryTheory