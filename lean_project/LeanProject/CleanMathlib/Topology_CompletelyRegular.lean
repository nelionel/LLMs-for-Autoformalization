import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.StoneCech
universe u
noncomputable section
open Set Topology Filter unitInterval
variable {X : Type u} [TopologicalSpace X] [T1Space X]
@[mk_iff]
class CompletelyRegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  completely_regular : ∀ (x : X), ∀ K : Set X, IsClosed K → x ∉ K →
    ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 K
instance CompletelyRegularSpace.instRegularSpace [CompletelyRegularSpace X] : RegularSpace X := by
  rw [regularSpace_iff]
  intro s a hs ha
  obtain ⟨f, cf, hf, hhf⟩ := CompletelyRegularSpace.completely_regular a s hs ha
  apply disjoint_of_map (f := f)
  apply Disjoint.mono (cf.tendsto_nhdsSet_nhds hhf) cf.continuousAt
  exact disjoint_nhds_nhds.mpr (hf.symm ▸ zero_ne_one).symm
instance NormalSpace.instCompletelyRegularSpace [NormalSpace X] : CompletelyRegularSpace X := by
  rw [completelyRegularSpace_iff]
  intro x K hK hx
  have cx : IsClosed {x} := T1Space.t1 x
  have d : Disjoint {x} K := by rwa [Set.disjoint_iff, subset_empty_iff, singleton_inter_eq_empty]
  let ⟨⟨f, cf⟩, hfx, hfK, hficc⟩ := exists_continuous_zero_one_of_isClosed cx hK d
  let g : X → I := fun x => ⟨f x, hficc x⟩
  have cg : Continuous g := cf.subtype_mk hficc
  have hgx : g x = 0 := Subtype.ext (hfx (mem_singleton_iff.mpr (Eq.refl x)))
  have hgK : EqOn g 1 K := fun k hk => Subtype.ext (hfK hk)
  exact ⟨g, cg, hgx, hgK⟩
@[mk_iff]
class T35Space (X : Type u) [TopologicalSpace X] extends T1Space X, CompletelyRegularSpace X : Prop
instance T35Space.instT3space [T35Space X] : T3Space X := {}
instance T4Space.instT35Space [T4Space X] : T35Space X := {}
lemma separatesPoints_continuous_of_t35Space [T35Space X] :
    SeparatesPoints (Continuous : Set (X → ℝ)) := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨fun x ↦ f x, continuous_subtype_val.comp f_cont, by aesop⟩
lemma separatesPoints_continuous_of_t35Space_Icc [T35Space X] :
    SeparatesPoints (Continuous : Set (X → I)) := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨f, f_cont, by aesop⟩
lemma injective_stoneCechUnit_of_t35Space [T35Space X] :
    Function.Injective (stoneCechUnit : X → StoneCech X) := by
  intros a b hab
  contrapose hab
  obtain ⟨f, fc, fab⟩ := separatesPoints_continuous_of_t35Space_Icc hab
  exact fun q ↦ fab (eq_if_stoneCechUnit_eq fc q)