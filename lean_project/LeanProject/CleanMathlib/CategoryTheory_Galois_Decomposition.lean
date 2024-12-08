import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
import Mathlib.Data.Finite.Sum
universe u₁ u₂ w
namespace CategoryTheory
open Limits Functor
variable {C : Type u₁} [Category.{u₂} C]
namespace PreGaloisCategory
section Decomposition
private lemma has_decomp_connected_components_aux_conn (X : C) [IsConnected X] :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Unit, fun _ ↦ X, fun _ ↦ 𝟙 X, mkCofanColimit _ (fun s ↦ s.inj ()), ?_⟩
  exact ⟨fun _ ↦ inferInstance, inferInstance⟩
private lemma has_decomp_connected_components_aux_initial (X : C) (h : IsInitial X) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Empty, fun _ ↦ X, fun _ ↦ 𝟙 X, ?_⟩
  use mkCofanColimit _ (fun s ↦ IsInitial.to h s.pt) (fun s ↦ by aesop)
    (fun s m _ ↦ IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩
variable [GaloisCategory C]
private lemma has_decomp_connected_components_aux (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (n : ℕ) : ∀ (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (f : ι → C)
    (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X → False
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h nhi
    obtain ⟨Z, u, ⟨c⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
    let t : ColimitCocone (pair Y Z) := { cocone := BinaryCofan.mk v u, isColimit := c }
    have hn1 : Nat.card (F.obj Y) < n := by
      rw [hn]
      exact lt_card_fiber_of_mono_of_notIso F v hvnoiso
    have i : X ≅ Y ⨿ Z := (colimit.isoColimitCocone t).symm
    have hnn : Nat.card (F.obj X) = Nat.card (F.obj Y) + Nat.card (F.obj Z) := by
      rw [card_fiber_eq_of_iso F i]
      exact card_fiber_coprod_eq_sum F Y Z
    have hn2 : Nat.card (F.obj Z) < n := by
      rw [hn, hnn, lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero (non_zero_card_fiber_of_not_initial F Y hni)
    let ⟨ι₁, f₁, g₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    let ⟨ι₂, f₂, g₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    refine ⟨ι₁ ⊕ ι₂, Sum.elim f₁ f₂,
      Cofan.combPairHoms (Cofan.mk Y g₁) (Cofan.mk Z g₂) (BinaryCofan.mk v u), ?_⟩
    use Cofan.combPairIsColimit hc₁ hc₂ c
    refine ⟨fun i ↦ ?_, inferInstance⟩
    cases i
    · exact hf₁ _
    · exact hf₂ _
  · simp only [not_forall, not_false_eq_true] at nhi
    obtain ⟨hi⟩ := nhi
    exact has_decomp_connected_components_aux_initial X hi
theorem has_decomp_connected_components (X : C) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → f i ⟶ X) (_ : IsColimit (Cofan.mk X g)),
      (∀ i, IsConnected (f i)) ∧ Finite ι := by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl
theorem has_decomp_connected_components' (X : C) :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (_ : ∐ f ≅ X), ∀ i, IsConnected (f i) := by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
lemma fiber_in_connected_component (X : C) (x : F.obj X) : ∃ (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ IsConnected Y ∧ Mono i := by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  have : Fintype ι := Fintype.ofFinite ι
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod.mono_inj _ (Cofan.mk X g) hl j⟩⟩
  subst h
  rfl
lemma connected_component_unique {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
    (b : F.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = F.map j b) [Mono i] [Mono j] :
    ∃ (f : A ≅ B), F.map f.hom a = b := by
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ FintypeCat.incl
  let e : F.obj Y ≃ { p : F.obj A × F.obj B // F.map i p.1 = F.map j p.2 } :=
    fiberPullbackEquiv F i j
  let y : F.obj Y := e.symm ⟨(a, b), h⟩
  have hn : IsInitial Y → False := not_initial_of_inhabited F y
  have : IsIso u := IsConnected.noTrivialComponent Y u hn
  have : IsIso v := IsConnected.noTrivialComponent Y v hn
  use (asIso u).symm ≪≫ asIso v
  have hu : G.map u y = a := by
    simp only [y, e, ← PreservesPullback.iso_hom_fst G, fiberPullbackEquiv, Iso.toEquiv_comp,
      Equiv.symm_trans_apply, Iso.toEquiv_symm_fun, types_comp_apply, inv_hom_id_apply]
    erw [Types.pullbackIsoPullback_inv_fst_apply (F.map i) (F.map j)]
  have hv : G.map v y = b := by
    simp only [y, e, ← PreservesPullback.iso_hom_snd G, fiberPullbackEquiv, Iso.toEquiv_comp,
      Equiv.symm_trans_apply, Iso.toEquiv_symm_fun, types_comp_apply, inv_hom_id_apply]
    erw [Types.pullbackIsoPullback_inv_snd_apply (F.map i) (F.map j)]
  rw [← hu, ← hv]
  show (F.toPrefunctor.map u ≫ F.toPrefunctor.map _) y = F.toPrefunctor.map v y
  simp only [← F.map_comp, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]
end Decomposition
section GaloisRep
variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
section GaloisRepAux
variable (X : C)
@[simp]
private noncomputable def selfProd : C := ∏ᶜ (fun _ : F.obj X ↦ X)
private noncomputable def mkSelfProdFib : F.obj (selfProd F X) :=
  (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X ↦ F.obj X)).symm id)
@[simp]
private lemma mkSelfProdFib_map_π (t : F.obj X) : F.map (Pi.π _ t) (mkSelfProdFib F X) = t := by
  rw [← congrFun (piComparison_comp_π F _ t), FintypeCat.comp_apply,
    ← PreservesProduct.iso_hom]
  simp only [mkSelfProdFib, FintypeCat.inv_hom_id_apply]
  exact Concrete.productEquiv_symm_apply_π.{w, w, w+1} (fun _ : F.obj X ↦ F.obj X) id t
variable {X} {A : C} (u : A ⟶ selfProd F X)
  (a : F.obj A) (h : F.map u a = mkSelfProdFib F X) {F}
include h
@[simp]
private noncomputable def selfProdProj (x : F.obj X) : A ⟶ X := u ≫ Pi.π _ x
variable {u a}
private lemma selfProdProj_fiber (x : F.obj X) :
    F.map (selfProdProj u x) a = x := by
  simp only [selfProdProj, selfProd, F.map_comp, FintypeCat.comp_apply, h]
  rw [mkSelfProdFib_map_π F X x]
variable [IsConnected A]
private noncomputable def fiberPerm (b : F.obj A) : F.obj X ≃ F.obj X := by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  show id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injective_of_isConnected F A X b hs
  rw [← selfProdProj_fiber h s, ← selfProdProj_fiber h t, h']
private noncomputable def selfProdPermIncl (b : F.obj A) : A ⟶ selfProd F X :=
  u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv
private instance [Mono u] (b : F.obj A) : Mono (selfProdPermIncl h b) := mono_comp _ _
private lemma selfProdTermIncl_fib_eq (b : F.obj A) :
    F.map u b = F.map (selfProdPermIncl h b) a := by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp, FintypeCat.comp_apply, h]
    convert_to F.map (selfProdProj u t) b =
      (F.map (Pi.map' (fiberPerm h b) fun _ ↦ 𝟙 X) ≫
      F.map (Pi.π (fun _ ↦ X) t)) (mkSelfProdFib F X)
    rw [← map_comp, Pi.map'_comp_π, Category.comp_id, mkSelfProdFib_map_π F X (fiberPerm h b t)]
    rfl
private lemma subobj_selfProd_trans [Mono u] (b : F.obj A) : ∃ (f : A ≅ A), F.map f.hom b = a := by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b
end GaloisRepAux
lemma exists_galois_representative (X : C) : ∃ (A : C) (a : F.obj A),
    IsGalois A ∧ Function.Bijective (fun (f : A ⟶ X) ↦ F.map f a) := by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y ↦ ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_trans h1 y
    use fi1 ≪≫ fi2.symm
    show F.map (fi1.hom ≫ fi2.inv) x = y
    simp only [map_comp, FintypeCat.comp_apply]
    rw [hfi1, ← hfi2]
    exact congr_fun (F.mapIso fi2).hom_inv_id y
  · refine ⟨evaluation_injective_of_isConnected F A X a, ?_⟩
    intro x
    use u ≫ Pi.π _ x
    exact (selfProdProj_fiber h1) x
lemma exists_hom_from_galois_of_fiber (X : C) (x : F.obj X) :
    ∃ (A : C) (f : A ⟶ X) (a : F.obj A), IsGalois A ∧ F.map f a = x := by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩
lemma exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A := by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩
include F in
lemma exists_hom_from_galois_of_connected (X : C) [IsConnected X] :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A :=
  exists_hom_from_galois_of_fiber_nonempty F X inferInstance
lemma natTrans_ext_of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
    (h : ∀ (X : C) [IsGalois X], t.app X = s.app X) :
    t = s := by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [FunctorToFintypeCat.naturality, FunctorToFintypeCat.naturality, h A]
end GaloisRep
end PreGaloisCategory
end CategoryTheory