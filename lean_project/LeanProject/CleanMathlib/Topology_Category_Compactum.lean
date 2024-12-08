import Mathlib.CategoryTheory.Monad.Types
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Data.Set.Constructions
universe u
open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits FiniteInter
open scoped Topology
local notation "β" => ofTypeMonad Ultrafilter
def Compactum :=
  Monad.Algebra β deriving Category, Inhabited
namespace Compactum
def forget : Compactum ⥤ Type* :=
  Monad.forget _ 
instance : forget.Faithful :=
  show (Monad.forget _).Faithful from inferInstance
noncomputable instance : CreatesLimits forget :=
  show CreatesLimits <| Monad.forget _ from inferInstance
def free : Type* ⥤ Compactum :=
  Monad.free _
def adj : free ⊣ forget :=
  Monad.adj _
instance : ConcreteCategory Compactum where forget := forget
instance : CoeSort Compactum Type* :=
  ⟨fun X => X.A⟩
instance {X Y : Compactum} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨fun f => f.f⟩
instance : HasLimits Compactum :=
  hasLimits_of_hasLimits_createsLimits forget
def str (X : Compactum) : Ultrafilter X → X :=
  X.a
def join (X : Compactum) : Ultrafilter (Ultrafilter X) → Ultrafilter X :=
  (β ).μ.app _
def incl (X : Compactum) : X → Ultrafilter X :=
  (β ).η.app _
@[simp]
theorem str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x := by
  change ((β ).η.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.unit]
  rfl
@[simp]
theorem str_hom_commute (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X) :
    f (X.str xs) = Y.str (map f xs) := by
  change (X.a ≫ f.f) _ = _
  rw [← f.h]
  rfl
@[simp]
theorem join_distrib (X : Compactum) (uux : Ultrafilter (Ultrafilter X)) :
    X.str (X.join uux) = X.str (map X.str uux) := by
  change ((β ).μ.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.assoc]
  rfl
instance {X : Compactum} : TopologicalSpace X.A where
  IsOpen U := ∀ F : Ultrafilter X, X.str F ∈ U → U ∈ F
  isOpen_univ _ _ := Filter.univ_sets _
  isOpen_inter _ _ h3 h4 _ h6 := Filter.inter_sets _ (h3 _ h6.1) (h4 _ h6.2)
  isOpen_sUnion := fun _ h1 _ ⟨T, hT, h2⟩ =>
    mem_of_superset (h1 T hT _ h2) (Set.subset_sUnion_of_mem hT)
theorem isClosed_iff {X : Compactum} (S : Set X) :
    IsClosed S ↔ ∀ F : Ultrafilter X, S ∈ F → X.str F ∈ S := by
  rw [← isOpen_compl_iff]
  constructor
  · intro cond F h
    by_contra c
    specialize cond F c
    rw [compl_mem_iff_not_mem] at cond
    contradiction
  · intro h1 F h2
    specialize h1 F
    cases' F.mem_or_compl_mem S with h h
    exacts [absurd (h1 h) h2, h]
instance {X : Compactum} : CompactSpace X := by
  constructor
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro F _
  refine ⟨X.str F, by tauto, ?_⟩
  rw [le_nhds_iff]
  intro S h1 h2
  exact h2 F h1
private def basic {X : Compactum} (A : Set X) : Set (Ultrafilter X) :=
  { F | A ∈ F }
private def cl {X : Compactum} (A : Set X) : Set X :=
  X.str '' basic A
private theorem basic_inter {X : Compactum} (A B : Set X) : basic (A ∩ B) = basic A ∩ basic B := by
  ext G
  constructor
  · intro hG
    constructor <;> filter_upwards [hG] with _
    exacts [And.left, And.right]
  · rintro ⟨h1, h2⟩
    exact inter_mem h1 h2
private theorem subset_cl {X : Compactum} (A : Set X) : A ⊆ cl A := fun a ha =>
  ⟨X.incl a, ha, by simp⟩
private theorem cl_cl {X : Compactum} (A : Set X) : cl (cl A) ⊆ cl A := by
  rintro _ ⟨F, hF, rfl⟩
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu → ssu := fun x ↦ ↑x
  let C0 : ssu := { Z | ∃ B ∈ F, X.str ⁻¹' B = Z }
  let AA := { G : Ultrafilter X | A ∈ G }
  let C1 := insert AA C0
  let C2 := finiteInterClosure C1
  have claim1 : ∀ (B) (_ : B ∈ C0) (C) (_ : C ∈ C0), B ∩ C ∈ C0 := by
    rintro B ⟨Q, hQ, rfl⟩ C ⟨R, hR, rfl⟩
    use Q ∩ R
    simp only [and_true, eq_self_iff_true, Set.preimage_inter]
    exact inter_sets _ hQ hR
  have claim2 : ∀ B ∈ C0, Set.Nonempty B := by
    rintro B ⟨Q, hQ, rfl⟩
    obtain ⟨q⟩ := Filter.nonempty_of_mem hQ
    use X.incl q
    simpa
  have claim3 : ∀ B ∈ C0, (AA ∩ B).Nonempty := by
    rintro B ⟨Q, hQ, rfl⟩
    have : (Q ∩ cl A).Nonempty := Filter.nonempty_of_mem (inter_mem hQ hF)
    rcases this with ⟨q, hq1, P, hq2, hq3⟩
    refine ⟨P, hq2, ?_⟩
    rw [← hq3] at hq1
    simpa
  suffices ∀ T : fsu, ι T ⊆ C1 → (⋂₀ ι T).Nonempty by
    obtain ⟨G, h1⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this
    use X.join G
    have : G.map X.str = F := Ultrafilter.coe_le_coe.1 fun S hS => h1 (Or.inr ⟨S, hS, rfl⟩)
    rw [join_distrib, this]
    exact ⟨h1 (Or.inl rfl), rfl⟩
  have claim4 := finiteInterClosure_finiteInter C1
  have claim5 : FiniteInter C0 := ⟨⟨_, univ_mem, Set.preimage_univ⟩, claim1⟩
  have claim6 : ∀ P ∈ C2, (P : Set (Ultrafilter X)).Nonempty := by
    suffices ∀ P ∈ C2, P ∈ C0 ∨ ∃ Q ∈ C0, P = AA ∩ Q by
      intro P hP
      cases' this P hP with h h
      · exact claim2 _ h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim3 _ hQ
    intro P hP
    exact claim5.finiteInterClosure_insert _ hP
  intro T hT
  suffices ⋂₀ ι T ∈ C2 by exact claim6 _ this
  apply claim4.finiteInter_mem T
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)
theorem isClosed_cl {X : Compactum} (A : Set X) : IsClosed (cl A) := by
  rw [isClosed_iff]
  intro F hF
  exact cl_cl _ ⟨F, hF, rfl⟩
theorem str_eq_of_le_nhds {X : Compactum} (F : Ultrafilter X) (x : X) : ↑F ≤ 𝓝 x → X.str F = x := by
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu → ssu := fun x ↦ ↑x
  let T0 : ssu := { S | ∃ A ∈ F, S = basic A }
  let AA := X.str ⁻¹' {x}
  let T1 := insert AA T0
  let T2 := finiteInterClosure T1
  intro cond
  have claim1 : ∀ A : Set X, IsClosed A → A ∈ F → x ∈ A := by
    intro A hA h
    by_contra H
    rw [le_nhds_iff] at cond
    specialize cond Aᶜ H hA.isOpen_compl
    rw [Ultrafilter.mem_coe, Ultrafilter.compl_mem_iff_not_mem] at cond
    contradiction
  have claim2 : ∀ A : Set X, A ∈ F → x ∈ cl A := by
    intro A hA
    exact claim1 (cl A) (isClosed_cl A) (mem_of_superset hA (subset_cl A))
  have claim3 : ∀ (S1) (_ : S1 ∈ T0) (S2) (_ : S2 ∈ T0), S1 ∩ S2 ∈ T0 := by
    rintro S1 ⟨S1, hS1, rfl⟩ S2 ⟨S2, hS2, rfl⟩
    exact ⟨S1 ∩ S2, inter_mem hS1 hS2, by simp [basic_inter]⟩
  have claim4 : ∀ S ∈ T0, (AA ∩ S).Nonempty := by
    rintro S ⟨S, hS, rfl⟩
    rcases claim2 _ hS with ⟨G, hG, hG2⟩
    exact ⟨G, hG2, hG⟩
  have claim5 : ∀ S ∈ T0, Set.Nonempty S := by
    rintro S ⟨S, hS, rfl⟩
    exact ⟨F, hS⟩
  have claim6 : ∀ S ∈ T2, Set.Nonempty S := by
    suffices ∀ S ∈ T2, S ∈ T0 ∨ ∃ Q ∈ T0, S = AA ∩ Q by
      intro S hS
      cases' this _ hS with h h
      · exact claim5 S h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim4 Q hQ
    intro S hS
    apply finiteInterClosure_insert
    · constructor
      · use Set.univ
        refine ⟨Filter.univ_sets _, ?_⟩
        ext
        refine ⟨?_, by tauto⟩
        · intro
          apply Filter.univ_sets
      · exact claim3
    · exact hS
  suffices ∀ F : fsu, ↑F ⊆ T1 → (⋂₀ ι F).Nonempty by
    obtain ⟨G, h1⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this
    have c1 : X.join G = F := Ultrafilter.coe_le_coe.1 fun P hP => h1 (Or.inr ⟨P, hP, rfl⟩)
    have c2 : G.map X.str = X.incl x := by
      refine Ultrafilter.coe_le_coe.1 fun P hP => ?_
      apply mem_of_superset (h1 (Or.inl rfl))
      rintro x ⟨rfl⟩
      exact hP
    simp [← c1, c2]
  intro T hT
  refine claim6 _ (finiteInter_mem (.finiteInterClosure_finiteInter _) _ ?_)
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)
theorem le_nhds_of_str_eq {X : Compactum} (F : Ultrafilter X) (x : X) : X.str F = x → ↑F ≤ 𝓝 x :=
  fun h => le_nhds_iff.mpr fun s hx hs => hs _ <| by rwa [h]
instance {X : Compactum} : T2Space X := by
  rw [t2_iff_ultrafilter]
  intro _ _ F hx hy
  rw [← str_eq_of_le_nhds _ _ hx, ← str_eq_of_le_nhds _ _ hy]
theorem lim_eq_str {X : Compactum} (F : Ultrafilter X) : F.lim = X.str F := by
  rw [Ultrafilter.lim_eq_iff_le_nhds, le_nhds_iff]
  tauto
theorem cl_eq_closure {X : Compactum} (A : Set X) : cl A = closure A := by
  ext
  rw [mem_closure_iff_ultrafilter]
  constructor
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩
theorem continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : Continuous f := by
  rw [continuous_iff_ultrafilter]
  intro x g h
  rw [Tendsto, ← coe_map]
  apply le_nhds_of_str_eq
  rw [← str_hom_commute, str_eq_of_le_nhds _ x _]
  apply h
noncomputable def ofTopologicalSpace (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : Compactum where
  A := X
  a := Ultrafilter.lim
  unit := by
    ext x
    exact lim_eq (pure_le_nhds _)
  assoc := by
    ext FF
    change Ultrafilter (Ultrafilter X) at FF
    set x := (Ultrafilter.map Ultrafilter.lim FF).lim with c1
    have c2 : ∀ (U : Set X) (F : Ultrafilter X), F.lim ∈ U → IsOpen U → U ∈ F := by
      intro U F h1 hU
      exact isOpen_iff_ultrafilter.mp hU _ h1 _ (Ultrafilter.le_nhds_lim _)
    have c3 : ↑(Ultrafilter.map Ultrafilter.lim FF) ≤ 𝓝 x := by
      rw [le_nhds_iff]
      intro U hx hU
      exact mem_coe.2 (c2 _ _ (by rwa [← c1]) hU)
    have c4 : ∀ U : Set X, x ∈ U → IsOpen U → { G : Ultrafilter X | U ∈ G } ∈ FF := by
      intro U hx hU
      suffices Ultrafilter.lim ⁻¹' U ∈ FF by
        apply mem_of_superset this
        intro P hP
        exact c2 U P hP hU
      exact @c3 U (IsOpen.mem_nhds hU hx)
    apply lim_eq
    rw [le_nhds_iff]
    exact c4
def homOfContinuous {X Y : Compactum} (f : X → Y) (cont : Continuous f) : X ⟶ Y :=
  { f
    h := by
      rw [continuous_iff_ultrafilter] at cont
      ext (F : Ultrafilter X)
      specialize cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)
      simp only [types_comp_apply, ofTypeFunctor_map]
      exact str_eq_of_le_nhds (Ultrafilter.map f F) _ cont }
end Compactum
def compactumToCompHaus : Compactum ⥤ CompHaus where
  obj X := { toTop := { α := X }, prop := trivial }
  map := fun f =>
    { toFun := f
      continuous_toFun := Compactum.continuous_of_hom _ }
namespace compactumToCompHaus
instance full : compactumToCompHaus.{u}.Full where
  map_surjective f := ⟨Compactum.homOfContinuous f.1 f.2, rfl⟩
instance faithful : compactumToCompHaus.Faithful where
  map_injective := by
    intro _ _ _ _ h
    apply Monad.Algebra.Hom.ext
    apply congrArg (fun f => f.toFun) h
def isoOfTopologicalSpace {D : CompHaus} :
    compactumToCompHaus.obj (Compactum.ofTopologicalSpace D) ≅ D where
  hom :=
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h => by
          rw [isOpen_iff_ultrafilter'] at h
          exact h }
  inv :=
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h1 => by
          rw [isOpen_iff_ultrafilter']
          intro _ h2
          exact h1 _ h2 }
instance essSurj : compactumToCompHaus.EssSurj :=
  { mem_essImage := fun X => ⟨Compactum.ofTopologicalSpace X, ⟨isoOfTopologicalSpace⟩⟩ }
instance isEquivalence : compactumToCompHaus.IsEquivalence where
end compactumToCompHaus
def compactumToCompHausCompForget :
    compactumToCompHaus ⋙ CategoryTheory.forget CompHaus ≅ Compactum.forget :=
  NatIso.ofComponents fun _ => eqToIso rfl
noncomputable instance CompHaus.forgetCreatesLimits : CreatesLimits (forget CompHaus) := by
  let e : forget CompHaus ≅ compactumToCompHaus.inv ⋙ Compactum.forget :=
    (((forget CompHaus).leftUnitor.symm ≪≫
    isoWhiskerRight compactumToCompHaus.asEquivalence.symm.unitIso (forget CompHaus)) ≪≫
    compactumToCompHaus.inv.associator compactumToCompHaus (forget CompHaus)) ≪≫
    isoWhiskerLeft _ compactumToCompHausCompForget
  exact createsLimitsOfNatIso e.symm
noncomputable instance Profinite.forgetCreatesLimits : CreatesLimits (forget Profinite) := by
  change CreatesLimits (profiniteToCompHaus ⋙ forget _)
  infer_instance