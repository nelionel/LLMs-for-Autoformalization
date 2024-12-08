import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
open CategoryTheory Limits Category
namespace HomologicalComplex
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')
namespace extend
section HomologyData
variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')
include hk hk' in
lemma comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) :
    φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e).d j' k' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk', Iso.inv_hom_id_assoc,
      ← cancel_mono (K.extendXIso e hk').inv, zero_comp, assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K.extend_d_from_eq_zero e j' k' j hj', comp_zero, comp_zero]
    rw [hk]
    exact hjk
namespace leftHomologyData
variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)
@[simp]
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])
noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')
variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)
include hi hi' hcone in
lemma lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt)
    (hf' : f' ≫ cone.ι = K.d i j)
    (f'' : (K.extend e).X i' ⟶ cone.pt)
    (hf'' : f'' ≫ cone.ι ≫ (extendXIso K e hj').inv = (K.extend e).d i' j')
    (φ : cone.pt ⟶ W) :
    f' ≫ φ = 0 ↔ f'' ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc, hf', ← cancel_mono (extendXIso K e hj').inv, assoc, assoc, hf'',
        K.extend_d_eq e hi'' hj']
    rw [← cancel_epi (K.extendXIso e hi'').hom, comp_zero, ← this, assoc]
  · have h₁ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₂ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      dsimp
      rw [← cancel_mono (extendXIso K e hj').inv, assoc, hf'', zero_comp, zero_comp,
        K.extend_d_to_eq_zero e i' j' j hj']
      rw [hi]
      exact hij
    simp [h₁, h₂]
include hi hi' in
lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _
noncomputable def cokernelCofork :
    CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) :=
  CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)
noncomputable def isColimitCokernelCofork :
    IsColimit (cokernelCofork K e hj' hi hi' hk hk' cone hcone cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)
end leftHomologyData
open leftHomologyData in
@[simps]
noncomputable def leftHomologyData (h : (K.sc' i j k).LeftHomologyData) :
    ((K.extend e).sc' i' j' k').LeftHomologyData where
  K := h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact h.wπ
  hπ := isColimitCokernelCofork K e hj' hi hi' hk hk' _ h.hi _ h.hπ
end HomologyData
end extend
end HomologicalComplex