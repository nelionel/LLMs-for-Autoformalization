import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Monad.Algebra
namespace CategoryTheory
open Category
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}
namespace Adjunction
@[simps! coe η μ]
def toMonad (h : L ⊣ R) : Monad C where
  toFunctor := L ⋙ R
  η := h.unit
  μ := whiskerRight (whiskerLeft L h.counit) R
  assoc X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit X := by
    dsimp
    rw [← R.map_comp]
    simp
@[simps coe ε δ]
def toComonad (h : L ⊣ R) : Comonad D where
  toFunctor := R ⋙ L
  ε := h.counit
  δ := whiskerRight (whiskerLeft R h.unit) L
  coassoc X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit X := by
    dsimp
    rw [← L.map_comp]
    simp
@[simps!]
def adjToMonadIso (T : Monad C) : T.adj.toMonad ≅ T :=
  MonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)
@[simps!]
def adjToComonadIso (G : Comonad C) : G.adj.toComonad ≅ G :=
  ComonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)
def unitAsIsoOfIso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : 𝟭 C ≅ L ⋙ R where
  hom := adj.unit
  inv :=  i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc, ← Iso.eq_inv_comp, comp_id, ← id_comp i.inv, Iso.eq_comp_inv, assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X
lemma isIso_unit_of_iso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit :=
  (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))
noncomputable def fullyFaithfulLOfCompIsoId (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : L.FullyFaithful :=
  haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit
def counitAsIsoOfIso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R ⋙ L ≅ 𝟭 D where
  hom := adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc, Iso.comp_inv_eq, id_comp, ← comp_id j.hom, ← Iso.inv_comp_eq, ← assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X
lemma isIso_counit_of_iso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit :=
  inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)
noncomputable def fullyFaithfulROfCompIsoId (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R.FullyFaithful :=
  haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit
end Adjunction
@[simps]
def Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.Algebra where
  obj X :=
    { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp, ← Adjunction.counit_naturality, R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp, Adjunction.counit_naturality, R.map_comp] }
@[simps]
def Monad.comparisonForget (h : L ⊣ R) : Monad.comparison h ⋙ h.toMonad.forget ≅ R where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
theorem Monad.left_comparison (h : L ⊣ R) : L ⋙ Monad.comparison h = h.toMonad.free :=
  rfl
instance [R.Faithful] (h : L ⊣ R) : (Monad.comparison h).Faithful where
  map_injective {_ _} _ _ w := R.map_injective (congr_arg Monad.Algebra.Hom.f w : _)
instance (T : Monad C) : (Monad.comparison T.adj).Full where
  map_surjective {_ _} f := ⟨⟨f.f, by simpa using f.h⟩, rfl⟩
instance (T : Monad C) : (Monad.comparison T.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        unit := by simpa using X.unit
        assoc := by simpa using X.assoc },
    ⟨Monad.Algebra.isoMk (Iso.refl _)⟩⟩
@[simps]
def Comonad.comparison (h : L ⊣ R) : C ⥤ h.toComonad.Coalgebra where
  obj X :=
    { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp, ← Adjunction.unit_naturality, L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }
@[simps]
def Comonad.comparisonForget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    Comonad.comparison h ⋙ h.toComonad.forget ≅ L where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
theorem Comonad.left_comparison (h : L ⊣ R) : R ⋙ Comonad.comparison h = h.toComonad.cofree :=
  rfl
instance Comonad.comparison_faithful_of_faithful [L.Faithful] (h : L ⊣ R) :
    (Comonad.comparison h).Faithful where
  map_injective {_ _} _ _ w := L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w : _)
instance (G : Comonad C) : (Comonad.comparison G.adj).Full where
  map_surjective f := ⟨⟨f.f, by simpa using f.h⟩, rfl⟩
instance (G : Comonad C) : (Comonad.comparison G.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        counit := by simpa using X.counit
        coassoc := by simpa using X.coassoc },
      ⟨Comonad.Coalgebra.isoMk (Iso.refl _)⟩⟩
class MonadicRightAdjoint (R : D ⥤ C) where
  L : C ⥤ D
  adj : L ⊣ R
  eqv : (Monad.comparison adj).IsEquivalence
def monadicLeftAdjoint (R : D ⥤ C) [MonadicRightAdjoint R] : C ⥤ D :=
  MonadicRightAdjoint.L (R := R)
def monadicAdjunction (R : D ⥤ C) [MonadicRightAdjoint R] :
    monadicLeftAdjoint R ⊣ R :=
  MonadicRightAdjoint.adj
instance (R : D ⥤ C) [MonadicRightAdjoint R] :
    (Monad.comparison (monadicAdjunction R)).IsEquivalence :=
  MonadicRightAdjoint.eqv
instance (R : D ⥤ C) [MonadicRightAdjoint R] : R.IsRightAdjoint :=
  (monadicAdjunction R).isRightAdjoint
noncomputable instance (T : Monad C) : MonadicRightAdjoint T.forget where
  adj := T.adj
  eqv := { }
class ComonadicLeftAdjoint (L : C ⥤ D) where
  R : D ⥤ C
  adj : L ⊣ R
  eqv : (Comonad.comparison adj).IsEquivalence
def comonadicRightAdjoint (L : C ⥤ D) [ComonadicLeftAdjoint L] : D ⥤ C :=
  ComonadicLeftAdjoint.R (L := L)
def comonadicAdjunction (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    L ⊣ comonadicRightAdjoint L :=
  ComonadicLeftAdjoint.adj
instance (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    (Comonad.comparison (comonadicAdjunction L)).IsEquivalence :=
  ComonadicLeftAdjoint.eqv
instance (L : C ⥤ D) [ComonadicLeftAdjoint L] : L.IsLeftAdjoint :=
  (comonadicAdjunction L).isLeftAdjoint
noncomputable instance (G : Comonad C) : ComonadicLeftAdjoint G.forget where
  adj := G.adj
  eqv := { }
instance μ_iso_of_reflective [Reflective R] : IsIso (reflectorAdjunction R).toMonad.μ := by
  dsimp
  infer_instance
instance δ_iso_of_coreflective [Coreflective R] : IsIso (coreflectorAdjunction R).toComonad.δ := by
  dsimp
  infer_instance
attribute [instance] MonadicRightAdjoint.eqv
attribute [instance] ComonadicLeftAdjoint.eqv
namespace Reflective
instance [Reflective R] (X : (reflectorAdjunction R).toMonad.Algebra) :
    IsIso ((reflectorAdjunction R).unit.app X.A) :=
  ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit, ← Functor.map_comp, ← Functor.map_comp]
        erw [X.unit]
        simp⟩⟩⟩
instance comparison_essSurj [Reflective R] :
    (Monad.comparison (reflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, comp_id]
  apply (X.unit_assoc _).symm
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : L ⊣ R) :
    (Monad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by aesop_cat⟩
end Reflective
namespace Coreflective
instance [Coreflective R] (X : (coreflectorAdjunction R).toComonad.Coalgebra) :
    IsIso ((coreflectorAdjunction R).counit.app X.A) :=
  ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit, ← Functor.map_comp, ← Functor.map_comp]
        erw [X.counit]
        simp, X.counit⟩⟩⟩
instance comparison_essSurj [Coreflective R] :
    (Comonad.comparison (coreflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A))
  rw [← cancel_mono ((coreflectorAdjunction R).counit.app X.A)]
  simp only [Adjunction.counit_naturality, Functor.comp_obj, Functor.id_obj,
    Adjunction.left_triangle_components_assoc, assoc]
  erw [X.counit]
  simp
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : R ⊣ L) :
    (Comonad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by aesop_cat⟩
end Coreflective
instance (priority := 100) monadicOfReflective [Reflective R] :
    MonadicRightAdjoint R where
  adj := reflectorAdjunction R
  eqv := { full := Reflective.comparison_full _ }
instance (priority := 100) comonadicOfCoreflective [Coreflective R] :
    ComonadicLeftAdjoint R where
  adj := coreflectorAdjunction R
  eqv := { full := Coreflective.comparison_full _ }
end CategoryTheory