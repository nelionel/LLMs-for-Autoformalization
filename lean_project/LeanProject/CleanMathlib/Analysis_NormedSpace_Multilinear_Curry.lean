import Mathlib.Analysis.NormedSpace.Multilinear.Basic
suppress_compilation
noncomputable section
open NNReal Finset Metric ContinuousMultilinearMap Fin Function
universe u v v' wE wE₁ wE' wEi wG wG'
variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE}
  {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
theorem ContinuousLinearMap.norm_map_tail_le
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (m 0) (tail m)‖ ≤ ‖f (m 0)‖ * ∏ i, ‖(tail m) i‖ := (f (m 0)).le_opNorm _
    _ ≤ ‖f‖ * ‖m 0‖ * ∏ i, ‖tail m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm _) <| by positivity
    _ = ‖f‖ * (‖m 0‖ * ∏ i, ‖(tail m) i‖) := by ring
    _ = ‖f‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_succ]
      rfl
theorem ContinuousMultilinearMap.norm_map_init_le
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (init m) (m (last n))‖ ≤ ‖f (init m)‖ * ‖m (last n)‖ := (f (init m)).le_opNorm _
    _ ≤ (‖f‖ * ∏ i, ‖(init m) i‖) * ‖m (last n)‖ :=
      (mul_le_mul_of_nonneg_right (f.le_opNorm _) (norm_nonneg _))
    _ = ‖f‖ * ((∏ i, ‖(init m) i‖) * ‖m (last n)‖) := mul_assoc _ _ _
    _ = ‖f‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_castSucc]
      rfl
theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (cons x m)‖ ≤ ‖f‖ * ∏ i, ‖cons x m i‖ := f.le_opNorm _
    _ = ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_succ]
      simp [mul_assoc]
theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    ‖f (snoc m x)‖ ≤ (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ :=
  calc
    ‖f (snoc m x)‖ ≤ ‖f‖ * ∏ i, ‖snoc m x i‖ := f.le_opNorm _
    _ = (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ := by
      rw [prod_univ_castSucc]
      simp [mul_assoc]
def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (@LinearMap.uncurryLeft 𝕜 n Ei G _ _ _ _ _
      (ContinuousMultilinearMap.toMultilinearMapLinear.comp f.toLinearMap)).mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m
@[simp]
theorem ContinuousLinearMap.uncurryLeft_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    f.uncurryLeft m = f (m 0) (tail m) :=
  rfl
def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearMap.mkContinuous
    { 
      toFun := fun x =>
        (f.toMultilinearMap.curryLeft x).mkContinuous (‖f‖ * ‖x‖) (f.norm_map_cons_le x)
      map_add' := fun x y => by
        ext m
        exact f.cons_add m x y
      map_smul' := fun c x => by
        ext m
        exact
          f.cons_smul m c x }
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
@[simp]
theorem ContinuousMultilinearMap.curryLeft_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl
@[simp]
theorem ContinuousLinearMap.curry_uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    f.uncurryLeft.curryLeft = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousLinearMap.uncurryLeft_apply, tail_cons,
    cons_zero]
@[simp]
theorem ContinuousMultilinearMap.uncurry_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryLeft.uncurryLeft = f :=
  ContinuousMultilinearMap.toMultilinearMap_injective <| f.toMultilinearMap.uncurry_curryLeft
variable (𝕜 Ei G)
def continuousMultilinearCurryLeftEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryLeft
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryLeft
      left_inv := ContinuousMultilinearMap.uncurry_curryLeft
      right_inv := ContinuousLinearMap.curry_uncurryLeft }
    (fun f => by
      simp only [LinearEquiv.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
variable {𝕜 Ei G}
@[simp]
theorem continuousMultilinearCurryLeftEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0) (v : Π i : Fin n, Ei i.succ) :
    continuousMultilinearCurryLeftEquiv 𝕜 Ei G f x v = f (cons x v) :=
  rfl
@[simp]
theorem continuousMultilinearCurryLeftEquiv_symm_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (v : Π i, Ei i) :
    (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm f v = f (v 0) (tail v) :=
  rfl
@[simp]
theorem ContinuousMultilinearMap.curryLeft_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f
@[simp]
theorem ContinuousLinearMap.uncurryLeft_norm
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ‖f.uncurryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f
def ContinuousMultilinearMap.uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →ₗ[𝕜] G) :=
    { toFun := fun m => (f m).toLinearMap
      map_update_add' := fun m i x y => by simp
      map_update_smul' := fun m i c x => by simp }
  (@MultilinearMap.uncurryRight 𝕜 n Ei G _ _ _ _ _ f').mkContinuous ‖f‖ fun m =>
    f.norm_map_init_le m
@[simp]
theorem ContinuousMultilinearMap.uncurryRight_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl
def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_update_add' := fun m i x y => by
        ext
        simp
      map_update_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
@[simp]
theorem ContinuousMultilinearMap.curryRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl
@[simp]
theorem ContinuousMultilinearMap.curry_uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply, ContinuousMultilinearMap.uncurryRight_apply,
    snoc_last, init_snoc]
@[simp]
theorem ContinuousMultilinearMap.uncurry_curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryRight.uncurryRight = f := by
  ext m
  rw [uncurryRight_apply, curryRight_apply, snoc_init_self]
variable (𝕜 Ei G)
def continuousMultilinearCurryRightEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryRight
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousMultilinearMap.uncurryRight
      left_inv := ContinuousMultilinearMap.uncurry_curryRight
      right_inv := ContinuousMultilinearMap.curry_uncurryRight }
    (fun f => by
      simp only [curryRight, LinearEquiv.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [uncurryRight, LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
variable (n G')
def continuousMultilinearCurryRightEquiv' : (G[×n.succ]→L[𝕜] G') ≃ₗᵢ[𝕜] G[×n]→L[𝕜] G →L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'
variable {n 𝕜 G Ei G'}
@[simp]
theorem continuousMultilinearCurryRightEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (v : Π i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    continuousMultilinearCurryRightEquiv 𝕜 Ei G f v x = f (snoc v x) :=
  rfl
@[simp]
theorem continuousMultilinearCurryRightEquiv_symm_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (v : Π i, Ei i) :
    (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v = f (init v) (v (last n)) :=
  rfl
@[simp]
theorem continuousMultilinearCurryRightEquiv_apply'
    (f : G[×n.succ]→L[𝕜] G') (v : Fin n → G) (x : G) :
    continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v x = f (snoc v x) :=
  rfl
@[simp]
theorem continuousMultilinearCurryRightEquiv_symm_apply'
    (f : G[×n]→L[𝕜] G →L[𝕜] G') (v : Fin (n + 1) → G) :
    (continuousMultilinearCurryRightEquiv' 𝕜 n G G').symm f v = f (init v) (v (last n)) :=
  rfl
@[simp]
theorem ContinuousMultilinearMap.curryRight_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f
@[simp]
theorem ContinuousMultilinearMap.uncurryRight_norm
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ‖f.uncurryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f
section
def ContinuousMultilinearMap.curry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G') :
    G' :=
  f 0
variable (𝕜 G) in
def ContinuousMultilinearMap.uncurry0 (x : G') : G[×0]→L[𝕜] G' :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x
variable (𝕜) in
@[simp]
theorem ContinuousMultilinearMap.uncurry0_apply (x : G') (m : Fin 0 → G) :
    ContinuousMultilinearMap.uncurry0 𝕜 G x m = x :=
  rfl
@[simp]
theorem ContinuousMultilinearMap.curry0_apply (f : G[×0]→L[𝕜] G') : f.curry0 = f 0 :=
  rfl
@[simp]
theorem ContinuousMultilinearMap.apply_zero_uncurry0 (f : G[×0]→L[𝕜] G') {x : Fin 0 → G} :
    ContinuousMultilinearMap.uncurry0 𝕜 G (f x) = f := by
  ext m
  simp [Subsingleton.elim x m]
theorem ContinuousMultilinearMap.uncurry0_curry0 (f : G[×0]→L[𝕜] G') :
    ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0 = f := by simp
variable (𝕜 G) in
theorem ContinuousMultilinearMap.curry0_uncurry0 (x : G') :
    (ContinuousMultilinearMap.uncurry0 𝕜 G x).curry0 = x :=
  rfl
variable (𝕜 G) in
@[simp]
theorem ContinuousMultilinearMap.uncurry0_norm (x : G') :
    ‖ContinuousMultilinearMap.uncurry0 𝕜 G x‖ = ‖x‖ :=
  norm_constOfIsEmpty _ _ _
@[simp]
theorem ContinuousMultilinearMap.fin0_apply_norm (f : G[×0]→L[𝕜] G') {x : Fin 0 → G} :
    ‖f x‖ = ‖f‖ := by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0‖ ≤ ‖f.curry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_uncurry0]
  simpa [-Matrix.zero_empty] using this
theorem ContinuousMultilinearMap.curry0_norm (f : G[×0]→L[𝕜] G') : ‖f.curry0‖ = ‖f‖ := by simp
variable (𝕜 G G')
def continuousMultilinearCurryFin0 : (G[×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  toFun f := ContinuousMultilinearMap.curry0 f
  invFun f := ContinuousMultilinearMap.uncurry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.curry0_norm
variable {𝕜 G G'}
@[simp]
theorem continuousMultilinearCurryFin0_apply (f : G[×0]→L[𝕜] G') :
    continuousMultilinearCurryFin0 𝕜 G G' f = f 0 :=
  rfl
@[simp]
theorem continuousMultilinearCurryFin0_symm_apply (x : G') (v : Fin 0 → G) :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x :=
  rfl
end
variable (𝕜 G G')
def continuousMultilinearCurryFin1 : (G[×1]→L[𝕜] G') ≃ₗᵢ[𝕜] G →L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').trans
    (continuousMultilinearCurryFin0 𝕜 G (G →L[𝕜] G'))
variable {𝕜 G G'}
@[simp]
theorem continuousMultilinearCurryFin1_apply (f : G[×1]→L[𝕜] G') (x : G) :
    continuousMultilinearCurryFin1 𝕜 G G' f x = f (Fin.snoc 0 x) :=
  rfl
@[simp]
theorem continuousMultilinearCurryFin1_symm_apply (f : G →L[𝕜] G') (v : Fin 1 → G) :
    (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0) :=
  rfl
namespace ContinuousMultilinearMap
variable (𝕜 G G')
@[simp]
theorem norm_domDomCongr (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :
    ‖domDomCongr σ f‖ = ‖f‖ := by
  simp only [norm_def, LinearEquiv.coe_mk, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, id_comp, comp_apply, Equiv.symm_apply_apply, id]
def domDomCongrₗᵢ (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }
variable {𝕜 G G'}
section
def currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')
@[simp]
theorem currySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G') (m : ι → G)
    (m' : ι' → G) : f.currySum m m' = f (Sum.elim m m') :=
  rfl
def uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G')) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G' :=
  MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using
      (f (m ∘ Sum.inl)).le_of_opNorm_le (f.le_opNorm _) (m ∘ Sum.inr)
@[simp]
theorem uncurrySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G'))
    (m : ι ⊕ ι' → G) : f.uncurrySum m = f (m ∘ Sum.inl) (m ∘ Sum.inr) :=
  rfl
variable (𝕜 ι ι' G G')
def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m)
      right_inv := fun f => by
        ext m₁ m₂
        rfl }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
end
section
variable (𝕜 G G') {k l : ℕ} {s : Finset (Fin n)}
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    (G[×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G[×k]→L[𝕜] G[×l]→L[𝕜] G' :=
  (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')
variable {𝕜 G G'}
@[simp]
theorem curryFinFinset_apply (hk : #s = k) (hl : #sᶜ = l) (f : G[×n]→L[𝕜] G')
    (mk : Fin k → G) (ml : Fin l → G) : curryFinFinset 𝕜 G G' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl
@[simp]
theorem curryFinFinset_symm_apply (hk : #s = k) (hl : #sᶜ = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (m : Fin n → G) : (curryFinFinset 𝕜 G G' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
theorem curryFinFinset_symm_apply_piecewise_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (x y : G) :
    (curryFinFinset 𝕜 G G' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y :=
  MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y
@[simp]
theorem curryFinFinset_symm_apply_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (x : G) :
    ((curryFinFinset 𝕜 G G' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
theorem curryFinFinset_apply_const (hk : #s = k) (hl : #sᶜ = l) (f : G[×n]→L[𝕜] G')
    (x y : G) : (curryFinFinset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]
end
end ContinuousMultilinearMap
namespace ContinuousLinearMap
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
noncomputable def continuousMultilinearMapOption (B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Option ι) ↦ (G × (Π i, E i))) F :=
  MultilinearMap.mkContinuous
  { toFun := fun p ↦ B (p none).1 (fun i ↦ (p i).2 i)
    map_update_add' := by
      intro inst v j x y
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i ↦ (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) ↦ (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B]
    map_update_smul' := by
      intro inst v j c x
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i ↦ (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) ↦ (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B] } (‖B‖) <| by
  intro b
  simp only [MultilinearMap.coe_mk, Fintype.prod_option]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  rw [← mul_assoc]
  gcongr with i _
  · apply (B.le_opNorm _).trans
    gcongr
    exact norm_fst_le _
  · exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
lemma continuousMultilinearMapOption_apply_eq_self (B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F)
    (a : G) (v : Π i, E i) : B.continuousMultilinearMapOption (fun _ ↦ (a, v)) = B a v := rfl
end ContinuousLinearMap