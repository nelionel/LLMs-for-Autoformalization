import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.Basic
open Topology
variable {R E F : Type*}
variable [CommRing R] [AddCommGroup E] [AddCommGroup F]
variable [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]
namespace LinearPMap
def IsClosed (f : E →ₗ.[R] F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))
variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]
def IsClosable (f : E →ₗ.[R] F) : Prop :=
  ∃ f' : LinearPMap R E F, f.graph.topologicalClosure = f'.graph
theorem IsClosed.isClosable {f : E →ₗ.[R] F} (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.submodule_topologicalClosure_eq⟩
theorem IsClosable.leIsClosable {f g : E →ₗ.[R] F} (hf : f.IsClosable) (hfg : g ≤ f) :
    g.IsClosable := by
  cases' hf with f' hf
  have : g.graph.topologicalClosure ≤ f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this hx) hx'
theorem IsClosable.existsUnique {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    ∃! f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph := by
  refine exists_unique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁, ← hy₂]
open Classical in
noncomputable def closure (f : E →ₗ.[R] F) : E →ₗ.[R] F :=
  if hf : f.IsClosable then hf.choose else f
theorem closure_def {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure = hf.choose := by
  simp [closure, hf]
theorem closure_def' {f : E →ₗ.[R] F} (hf : ¬f.IsClosable) : f.closure = f := by simp [closure, hf]
theorem IsClosable.graph_closure_eq_closure_graph {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    f.graph.topologicalClosure = f.closure.graph := by
  rw [closure_def hf]
  exact hf.choose_spec
theorem le_closure (f : E →ₗ.[R] F) : f ≤ f.closure := by
  by_cases hf : f.IsClosable
  · refine le_of_le_graph ?_
    rw [← hf.graph_closure_eq_closure_graph]
    exact (graph f).le_topologicalClosure
  rw [closure_def' hf]
theorem IsClosable.closure_mono {f g : E →ₗ.[R] F} (hg : g.IsClosable) (h : f ≤ g) :
    f.closure ≤ g.closure := by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)
theorem IsClosable.closure_isClosed {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosed := by
  rw [IsClosed, ← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure
theorem IsClosable.closureIsClosable {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosable :=
  hf.closure_isClosed.isClosable
theorem isClosable_iff_exists_closed_extension {f : E →ₗ.[R] F} :
    f.IsClosable ↔ ∃ g : E →ₗ.[R] F, g.IsClosed ∧ f ≤ g :=
  ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩
structure HasCore (f : E →ₗ.[R] F) (S : Submodule R E) : Prop where
  le_domain : S ≤ f.domain
  closure_eq : (f.domRestrict S).closure = f
theorem hasCore_def {f : E →ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) :
    (f.domRestrict S).closure = f :=
  h.2
theorem closureHasCore (f : E →ₗ.[R] F) : f.closure.HasCore f.domain := by
  refine ⟨f.le_closure.1, ?_⟩
  congr
  ext x y hxy
  · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
    intro hx
    exact f.le_closure.1 hx
  let z : f.closure.domain := ⟨y.1, f.le_closure.1 y.2⟩
  have hyz : (y : E) = z := by simp
  rw [f.le_closure.2 hyz]
  exact domRestrict_apply (hxy.trans hyz)
section Inverse
variable {f : E →ₗ.[R] F}
theorem closure_inverse_graph (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.closure.inverse.graph = f.inverse.graph.topologicalClosure := by
  rw [inverse_graph hf, inverse_graph hcf, ← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antisymm
  have h1 := Set.image_equiv_eq_preimage_symm f.graph (LinearEquiv.prodComm R E F).toEquiv
  have h2 := Set.image_equiv_eq_preimage_symm (_root_.closure f.graph)
    (LinearEquiv.prodComm R E F).toEquiv
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.prodComm_apply,
    LinearEquiv.coe_toEquiv_symm] at h1 h2
  rw [h1, h2]
  apply continuous_swap.closure_preimage_subset
theorem inverse_isClosable_iff (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable) :
    f.inverse.IsClosable ↔ LinearMap.ker f.closure.toFun = ⊥ := by
  constructor
  · intro ⟨f', h⟩
    rw [LinearMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [toFun_eq_coe, eq_comm, image_iff] at hx'
    have : (0, x) ∈ graph f' := by
      rw [← h, inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hx'
      apply image_closure_subset_closure_image continuous_swap
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      exact ⟨x, 0, hx', rfl, rfl⟩
    exact graph_fst_eq_zero_snd f' this rfl
  · intro h
    use f.closure.inverse
    exact (closure_inverse_graph hf hf' h).symm
theorem inverse_closure (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.inverse.closure = f.closure.inverse := by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf,
    ((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]
end Inverse
end LinearPMap