import Mathlib.AlgebraicTopology.SplitSimplicialObject
import Mathlib.AlgebraicTopology.DoldKan.PInfty
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory
  SimplicialObject Opposite CategoryTheory.Idempotents Simplicial DoldKan
namespace AlgebraicTopology
namespace DoldKan
variable {C : Type*} [Category C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ Δ' Δ'' : SimplexCategory}
@[nolint unusedArguments]
def Isδ₀ {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] : Prop :=
  Δ.len = Δ'.len + 1 ∧ i.toOrderHom 0 ≠ 0
namespace Isδ₀
theorem iff {j : ℕ} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0 := by
  constructor
  · rintro ⟨_, h₂⟩
    by_contra h
    exact h₂ (Fin.succAbove_ne_zero_zero h)
  · rintro rfl
    exact ⟨rfl, by dsimp; exact Fin.succ_ne_zero (0 : Fin (j + 1))⟩
theorem eq_δ₀ {n : ℕ} {i : ([n] : SimplexCategory) ⟶ [n + 1]} [Mono i] (hi : Isδ₀ i) :
    i = SimplexCategory.δ 0 := by
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono i
  rw [iff] at hi
  rw [hi]
end Isδ₀
namespace Γ₀
namespace Obj
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.X A.1.unop.len
def obj₂ (K : ChainComplex C ℕ) (Δ : SimplexCategoryᵒᵖ) [HasFiniteCoproducts C] : C :=
  ∐ fun A : Splitting.IndexSet Δ => summand K Δ A
namespace Termwise
def mapMono (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    K.X Δ.len ⟶ K.X Δ'.len := by
  by_cases Δ = Δ'
  · exact eqToHom (by congr)
  · by_cases Isδ₀ i
    · exact K.d Δ.len Δ'.len
    · exact 0
variable (Δ)
theorem mapMono_id : mapMono K (𝟙 Δ) = 𝟙 _ := by
  unfold mapMono
  simp only [eq_self_iff_true, eqToHom_refl, dite_eq_ite, if_true]
variable {Δ}
theorem mapMono_δ₀' (i : Δ' ⟶ Δ) [Mono i] (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len := by
  unfold mapMono
  suffices Δ ≠ Δ' by
    simp only [dif_neg this, dif_pos hi]
  rintro rfl
  simpa only [self_eq_add_right, Nat.one_ne_zero] using hi.1
@[simp]
theorem mapMono_δ₀ {n : ℕ} : mapMono K (δ (0 : Fin (n + 2))) = K.d (n + 1) n :=
  mapMono_δ₀' K _ (by rw [Isδ₀.iff])
theorem mapMono_eq_zero (i : Δ' ⟶ Δ) [Mono i] (h₁ : Δ ≠ Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0 := by
  unfold mapMono
  rw [Ne] at h₁
  split_ifs
  rfl
variable {K K'}
@[reassoc (attr := simp)]
theorem mapMono_naturality (i : Δ ⟶ Δ') [Mono i] :
    mapMono K i ≫ f.f Δ.len = f.f Δ'.len ≫ mapMono K' i := by
  unfold mapMono
  split_ifs with h
  · subst h
    simp only [id_comp, eqToHom_refl, comp_id]
  · rw [HomologicalComplex.Hom.comm]
  · rw [zero_comp, comp_zero]
variable (K)
@[reassoc (attr := simp)]
theorem mapMono_comp (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [Mono i'] [Mono i] :
    mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i) := by
  by_cases h₁ : Δ = Δ'
  · subst h₁
    simp only [SimplexCategory.eq_id_of_mono i, comp_id, id_comp, mapMono_id K, eqToHom_refl]
  by_cases h₂ : Δ' = Δ''
  · subst h₂
    simp only [SimplexCategory.eq_id_of_mono i', comp_id, id_comp, mapMono_id K, eqToHom_refl]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i h₁)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂)
  have eq : Δ.len = Δ''.len + (k + k' + 2) := by omega
  rw [mapMono_eq_zero K (i' ≫ i) _ _]; rotate_left
  · by_contra h
    simp only [self_eq_add_right, h, add_eq_zero, and_false, reduceCtorEq] at eq
  · by_contra h
    simp only [h.1, add_right_inj] at eq
    omega
  by_cases h₃ : Isδ₀ i
  · by_cases h₄ : Isδ₀ i'
    · rw [mapMono_δ₀' K i h₃, mapMono_δ₀' K i' h₄, HomologicalComplex.d_comp_d]
    · simp only [mapMono_eq_zero K i' h₂ h₄, comp_zero]
  · simp only [mapMono_eq_zero K i h₁ h₃, zero_comp]
end Termwise
variable [HasFiniteCoproducts C]
def map (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') : obj₂ K Δ ⟶ obj₂ K Δ' :=
  Sigma.desc fun A =>
    Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K Δ') (A.pull θ)
@[reassoc]
theorem map_on_summand₀ {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'}
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K i ≫ Sigma.ι (summand K Δ') (Splitting.IndexSet.mk e) := by
  simp only [map, colimit.ι_desc, Cofan.mk_ι_app]
  have h := SimplexCategory.image_eq fac
  subst h
  congr
  · exact SimplexCategory.image_ι_eq fac
  · dsimp only [SimplicialObject.Splitting.IndexSet.pull]
    congr
    exact SimplexCategory.factorThruImage_eq fac
@[reassoc]
theorem map_on_summand₀' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K _) (A.pull θ) :=
  map_on_summand₀ K A (A.fac_pull θ)
end Obj
variable [HasFiniteCoproducts C]
@[simps]
def obj (K : ChainComplex C ℕ) : SimplicialObject C where
  obj Δ := Obj.obj₂ K Δ
  map θ := Obj.map K θ
  map_id Δ := colimit.hom_ext (fun ⟨A⟩ => by
    dsimp
    have fac : A.e ≫ 𝟙 A.1.unop = (𝟙 Δ).unop ≫ A.e := by rw [unop_id, comp_id, id_comp]
    erw [Obj.map_on_summand₀ K A fac, Obj.Termwise.mapMono_id, id_comp, comp_id]
    rfl)
  map_comp {Δ'' Δ' Δ} θ' θ := colimit.hom_ext (fun ⟨A⟩ => by
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc]
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc, ←
      image.fac (θ.unop ≫ factorThruImage (θ'.unop ≫ A.e)), assoc] at fac
    simp only [Obj.map_on_summand₀'_assoc K A θ', Obj.map_on_summand₀' K _ θ,
      Obj.Termwise.mapMono_comp_assoc, Obj.map_on_summand₀ K A fac]
    rfl)
def splitting (K : ChainComplex C ℕ) : SimplicialObject.Splitting (Γ₀.obj K) where
  N n := K.X n
  ι n := Sigma.ι (Γ₀.Obj.summand K (op [n])) (Splitting.IndexSet.id (op [n]))
  isColimit' Δ := IsColimit.ofIsoColimit (colimit.isColimit _) (Cofan.ext (Iso.refl _) (by
      intro A
      dsimp [Splitting.cofan']
      rw [comp_id, Γ₀.Obj.map_on_summand₀ K (SimplicialObject.Splitting.IndexSet.id A.1)
        (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _ by rfl), Γ₀.Obj.Termwise.mapMono_id]
      dsimp
      rw [id_comp]
      rfl))
@[reassoc]
theorem Obj.map_on_summand {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ')
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    ((Γ₀.splitting K).cofan Δ).inj A ≫ (Γ₀.obj K).map θ =
      Γ₀.Obj.Termwise.mapMono K i ≫ ((Γ₀.splitting K).cofan Δ').inj (Splitting.IndexSet.mk e) := by
  dsimp [Splitting.cofan]
  change (_ ≫ (Γ₀.obj K).map A.e.op) ≫ (Γ₀.obj K).map θ = _
  rw [assoc, ← Functor.map_comp]
  dsimp [splitting]
  erw [Γ₀.Obj.map_on_summand₀ K (Splitting.IndexSet.id A.1)
    (show e ≫ i = ((Splitting.IndexSet.e A).op ≫ θ).unop ≫ 𝟙 _ by rw [comp_id, fac]; rfl),
    Γ₀.Obj.map_on_summand₀ K (Splitting.IndexSet.id (op Δ''))
      (show e ≫ 𝟙 Δ'' = e.op.unop ≫ 𝟙 _ by simp), Termwise.mapMono_id, id_comp]
@[reassoc]
theorem Obj.map_on_summand' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    ((splitting K).cofan Δ).inj A ≫ (obj K).map θ =
      Obj.Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫
        ((splitting K).cofan Δ').inj (A.pull θ) := by
  apply Obj.map_on_summand
  apply image.fac
@[reassoc]
theorem Obj.mapMono_on_summand_id {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    ((splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ)) ≫ (obj K).map i.op =
      Obj.Termwise.mapMono K i ≫ ((splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ')) :=
  Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) i.op (rfl : 𝟙 _ ≫ i = i ≫ 𝟙 _)
@[reassoc]
theorem Obj.map_epi_on_summand_id {Δ Δ' : SimplexCategory} (e : Δ' ⟶ Δ) [Epi e] :
    ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ)) ≫ (Γ₀.obj K).map e.op =
      ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.mk e) := by
  simpa only [Γ₀.Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) e.op
      (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ),
    Γ₀.Obj.Termwise.mapMono_id] using id_comp _
@[simps]
def map {K K' : ChainComplex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' where
  app Δ := (Γ₀.splitting K).desc Δ fun A => f.f A.1.unop.len ≫
    ((Γ₀.splitting K').cofan _).inj A
  naturality {Δ' Δ} θ := by
    apply (Γ₀.splitting K).hom_ext'
    intro A
    simp only [(splitting K).ι_desc_assoc, Obj.map_on_summand'_assoc K _ θ, (splitting K).ι_desc,
      assoc, Obj.map_on_summand' K' _ θ]
    apply Obj.Termwise.mapMono_naturality_assoc
end Γ₀
variable [HasFiniteCoproducts C]
@[simps]
def Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C where
  obj K := SimplicialObject.Split.mk' (Γ₀.splitting K)
  map {K K'} f :=
    { F := Γ₀.map f
      f := f.f
      comm := fun n => by
        dsimp
        simp only [← Splitting.cofan_inj_id, (Γ₀.splitting K).ι_desc]
        rfl }
@[simps!]
def Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀' ⋙ Split.forget _
@[simps!]
def Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  (CategoryTheory.Idempotents.functorExtension₂ _ _).obj Γ₀
theorem HigherFacesVanish.on_Γ₀_summand_id (K : ChainComplex C ℕ) (n : ℕ) :
    @HigherFacesVanish C _ _ (Γ₀.obj K) _ n (n + 1)
      (((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op [n + 1]))) := by
  intro j _
  have eq := Γ₀.Obj.mapMono_on_summand_id K (SimplexCategory.δ j.succ)
  rw [Γ₀.Obj.Termwise.mapMono_eq_zero K, zero_comp] at eq; rotate_left
  · intro h
    exact (Nat.succ_ne_self n) (congr_arg SimplexCategory.len h)
  · exact fun h => Fin.succ_ne_zero j (by simpa only [Isδ₀.iff] using h)
  exact eq
@[reassoc (attr := simp)]
theorem PInfty_on_Γ₀_splitting_summand_eq_self (K : ChainComplex C ℕ) {n : ℕ} :
    ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op [n])) ≫
      (PInfty : K[Γ₀.obj K] ⟶ _).f n =
      ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op [n])) := by
  rw [PInfty_f]
  rcases n with _|n
  · simpa only [P_f_0_eq] using comp_id _
  · exact (HigherFacesVanish.on_Γ₀_summand_id K n).comp_P_eq_self
end DoldKan
end AlgebraicTopology