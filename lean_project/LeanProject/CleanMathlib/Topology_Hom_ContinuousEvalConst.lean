import Mathlib.Topology.Constructions
open scoped Topology
open Filter
class ContinuousEvalConst (F : Type*) (α X : outParam Type*) [FunLike F α X]
    [TopologicalSpace F] [TopologicalSpace X] : Prop where
  continuous_eval_const (x : α) : Continuous fun f : F ↦ f x
export ContinuousEvalConst (continuous_eval_const)
section ContinuousEvalConst
variable {F α X Z : Type*} [FunLike F α X] [TopologicalSpace F] [TopologicalSpace X]
  [ContinuousEvalConst F α X] [TopologicalSpace Z] {f : Z → F} {s : Set Z} {z : Z}
theorem ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEvalConst F' α X where
  continuous_eval_const x := by simpa only [← hf] using (continuous_eval_const x).comp hc
@[continuity, fun_prop]
protected theorem Continuous.eval_const (hf : Continuous f) (x : α) : Continuous (f · x) :=
  (continuous_eval_const x).comp hf
theorem continuous_coeFun : Continuous (DFunLike.coe : F → α → X) :=
  continuous_pi continuous_eval_const
protected theorem Continuous.coeFun (hf : Continuous f) : Continuous fun z ↦ ⇑(f z) :=
  continuous_pi hf.eval_const
protected theorem Filter.Tendsto.eval_const {ι : Type*} {l : Filter ι} {f : ι → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) (a : α) : Tendsto (f · a) l (𝓝 (g a)) :=
  ((continuous_id.eval_const a).tendsto _).comp hf
protected theorem Filter.Tendsto.coeFun {ι : Type*} {l : Filter ι} {f : ι → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) : Tendsto (fun i ↦ ⇑(f i)) l (𝓝 ⇑g) :=
  (continuous_id.coeFun.tendsto _).comp hf
protected nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : α) :
    ContinuousAt (f · x) z :=
  hf.eval_const x
protected nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) :
    ContinuousAt (fun z ↦ ⇑(f z)) z :=
  hf.coeFun
protected nonrec theorem ContinuousWithinAt.eval_const (hf : ContinuousWithinAt f s z) (x : α) :
    ContinuousWithinAt (f · x) s z :=
  hf.eval_const x
protected nonrec theorem ContinuousWithinAt.coeFun (hf : ContinuousWithinAt f s z) :
    ContinuousWithinAt (fun z ↦ ⇑(f z)) s z :=
  hf.coeFun
protected theorem ContinuousOn.eval_const (hf : ContinuousOn f s) (x : α) :
    ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x
protected theorem ContinuousOn.coeFun (hf : ContinuousOn f s) (x : α) : ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x
end ContinuousEvalConst