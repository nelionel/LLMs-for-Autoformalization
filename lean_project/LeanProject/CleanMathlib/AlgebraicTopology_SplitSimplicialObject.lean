import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Data.Fintype.Sigma
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite SimplexCategory
open Simplicial
universe u
variable {C : Type*} [Category C]
namespace SimplicialObject
namespace Splitting
def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  ΣΔ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }
namespace IndexSet
@[simps]
def mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ) :=
  ⟨op Δ', f, inferInstance⟩
variable {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
def e :=
  A.2.1
instance : Epi A.e :=
  A.2.2
theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := rfl
theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) :
    A₁ = A₂ := by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]
instance : Fintype (IndexSet Δ) :=
  Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi (inferInstance : Epi A.e))⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ → Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) → Fin (k + 1))
    (by
      rintro ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁
      induction' Δ₁ using Opposite.rec with Δ₁
      induction' Δ₂ using Opposite.rec with Δ₂
      simp only [unop_op, Sigma.mk.inj_iff, Fin.mk.injEq] at h₁
      have h₂ : Δ₁ = Δ₂ := by
        ext1
        simpa only [Fin.mk_eq_mk] using h₁.1
      subst h₂
      refine ext _ _ rfl ?_
      ext : 2
      exact eq_of_heq h₁.2)
variable (Δ)
@[simps]
def id : IndexSet Δ :=
  ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩
instance : Inhabited (IndexSet Δ) :=
  ⟨id Δ⟩
variable {Δ}
@[simp]
def EqId : Prop :=
  A = id _
theorem eqId_iff_eq : A.EqId ↔ A.1 = Δ := by
  constructor
  · intro h
    dsimp at h
    rw [h]
    rfl
  · intro h
    rcases A with ⟨_, ⟨f, hf⟩⟩
    simp only at h
    subst h
    refine ext _ _ rfl ?_
    haveI := hf
    simp only [eqToHom_refl, comp_id]
    exact eq_id_of_epi f
theorem eqId_iff_len_eq : A.EqId ↔ A.1.unop.len = Δ.unop.len := by
  rw [eqId_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← unop_inj_iff]
    ext
    exact h
theorem eqId_iff_len_le : A.EqId ↔ Δ.unop.len ≤ A.1.unop.len := by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi (inferInstance : Epi A.e))
theorem eqId_iff_mono : A.EqId ↔ Mono A.e := by
  constructor
  · intro h
    dsimp at h
    subst h
    dsimp only [id, e]
    infer_instance
  · intro h
    rw [eqId_iff_len_le]
    exact len_le_of_mono h
@[simps]
def epiComp {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    IndexSet Δ₂ :=
  ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩
variable {Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
def pull : IndexSet Δ' :=
  mk (factorThruImage (θ.unop ≫ A.e))
@[reassoc]
theorem fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e :=
  image.fac _
end IndexSet
variable (N : ℕ → C) (Δ : SimplexCategoryᵒᵖ) (X : SimplicialObject C) (φ : ∀ n, N n ⟶ X _[n])
@[simp, nolint unusedArguments]
def summand (A : IndexSet Δ) : C :=
  N A.1.unop.len
def cofan' (Δ : SimplexCategoryᵒᵖ) : Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)
end Splitting
structure Splitting (X : SimplicialObject C) where
  N : ℕ → C
  ι : ∀ n, N n ⟶ X _[n]
  isColimit' : ∀ Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)
namespace Splitting
variable {X Y : SimplicialObject C} (s : Splitting X)
def cofan (Δ : SimplexCategoryᵒᵖ) : Cofan (summand s.N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)
def isColimit (Δ : SimplexCategoryᵒᵖ) : IsColimit (s.cofan Δ) := s.isColimit' Δ
@[reassoc]
theorem cofan_inj_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj  A = s.ι A.1.unop.len ≫ X.map A.e.op := rfl
theorem cofan_inj_id (n : ℕ) : (s.cofan _).inj (IndexSet.id (op [n])) = s.ι n := by
  erw [cofan_inj_eq, X.map_id, comp_id]
  rfl
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _[n] :=
  s.ι n ≫ f.app (op [n])
@[reassoc (attr := simp)]
theorem cofan_inj_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op := by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  rw [NatTrans.naturality]
theorem hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
    (h : ∀ A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h
theorem hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g := by
  ext Δ
  apply s.hom_ext'
  intro A
  induction' Δ using Opposite.rec with Δ
  induction' Δ using SimplexCategory.rec with n
  dsimp
  simp only [s.cofan_inj_comp_app, h]
def desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z) :
    X.obj Δ ⟶ Z :=
  Cofan.IsColimit.desc (s.isColimit Δ) F
@[reassoc (attr := simp)]
theorem ι_desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
    (A : IndexSet Δ) : (s.cofan Δ).inj A ≫ s.desc Δ F = F A := by
  apply Cofan.IsColimit.fac
@[simps]
def ofIso (e : X ≅ Y) : Splitting Y where
  N := s.N
  ι n := s.ι n ≫ e.hom.app (op [n])
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))
@[reassoc]
theorem cofan_inj_epi_naturality {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
    [Epi p.unop] : (s.cofan Δ₁).inj A ≫ X.map p = (s.cofan Δ₂).inj (A.epiComp p) := by
  dsimp [cofan]
  rw [assoc, ← X.map_comp]
  rfl
end Splitting
variable (C)
@[ext]
structure Split where
  X : SimplicialObject C
  s : Splitting X
namespace Split
variable {C}
@[simps]
def mk' {X : SimplicialObject C} (s : Splitting X) : Split C :=
  ⟨X, s⟩
structure Hom (S₁ S₂ : Split C) where
  F : S₁.X ⟶ S₂.X
  f : ∀ n : ℕ, S₁.s.N n ⟶ S₂.s.N n
  comm : ∀ n : ℕ, S₁.s.ι n ≫ F.app (op [n]) = f n ≫ S₂.s.ι n := by aesop_cat
@[ext]
theorem Hom.ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ := by
  rcases Φ₁ with ⟨F₁, f₁, c₁⟩
  rcases Φ₂ with ⟨F₂, f₂, c₂⟩
  have h' : f₁ = f₂ := by
    ext
    apply h
  subst h'
  simp only [mk.injEq, and_true]
  apply S₁.s.hom_ext
  intro n
  dsimp
  rw [c₁, c₂]
attribute [simp, reassoc] Hom.comm
end Split
instance : Category (Split C) where
  Hom := Split.Hom
  id S :=
    { F := 𝟙 _
      f := fun _ => 𝟙 _ }
  comp Φ₁₂ Φ₂₃ :=
    { F := Φ₁₂.F ≫ Φ₂₃.F
      f := fun n => Φ₁₂.f n ≫ Φ₂₃.f n
      comm := fun n => by
        dsimp
        simp only [assoc, Split.Hom.comm_assoc, Split.Hom.comm] }
variable {C}
namespace Split
@[ext]
theorem hom_ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ :=
  Hom.ext _ _ h
theorem congr_F {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.f = Φ₂.f := by rw [h]
theorem congr_f {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : ℕ) : Φ₁.f n = Φ₂.f n := by
  rw [h]
@[simp]
theorem id_F (S : Split C) : (𝟙 S : S ⟶ S).F = 𝟙 S.X :=
  rfl
@[simp]
theorem id_f (S : Split C) (n : ℕ) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n) :=
  rfl
@[simp]
theorem comp_F {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) :
    (Φ₁₂ ≫ Φ₂₃).F = Φ₁₂.F ≫ Φ₂₃.F :=
  rfl
@[simp]
theorem comp_f {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : ℕ) :
    (Φ₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n :=
  rfl
@[reassoc (attr := simp 1100)]
theorem cofan_inj_naturality_symm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
    (A : Splitting.IndexSet Δ) :
    (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ = Φ.f A.1.unop.len ≫ (S₂.s.cofan Δ).inj A := by
  rw [S₁.s.cofan_inj_eq, S₂.s.cofan_inj_eq, assoc, Φ.F.naturality, ← Φ.comm_assoc]
variable (C)
@[simps]
def forget : Split C ⥤ SimplicialObject C where
  obj S := S.X
  map Φ := Φ.F
@[simps]
def evalN (n : ℕ) : Split C ⥤ C where
  obj S := S.s.N n
  map Φ := Φ.f n
@[simps]
def natTransCofanInj {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) :
    evalN C A.1.unop.len ⟶ forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where
  app S := (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm
end Split
end SimplicialObject