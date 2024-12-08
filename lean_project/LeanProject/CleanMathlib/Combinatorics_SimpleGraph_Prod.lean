import Mathlib.Combinatorics.SimpleGraph.Path
variable {α β γ : Type*}
namespace SimpleGraph
variable {G : SimpleGraph α} {H : SimpleGraph β}
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm x y := by simp [and_comm, or_comm, eq_comm, adj_comm]
  loopless x := by simp
infixl:70 " □ " => boxProd
@[simp]
theorem boxProd_adj {x y : α × β} :
    (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl
theorem boxProd_adj_left {a₁ : α} {b : β} {a₂ : α} :
    (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]
theorem boxProd_adj_right {a : α} {b₁ b₂ : β} : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]
theorem boxProd_neighborSet (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} ∪ {x.1} ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]
variable (G H)
@[simps!]
def boxProdComm : G □ H ≃g H □ G := ⟨Equiv.prodComm _ _, or_comm⟩
@[simps!]
def boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩
@[simps]
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left
@[simps]
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right
namespace Walk
variable {G}
protected def boxProdLeft {a₁ a₂ : α} (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom
variable (G) {H}
protected def boxProdRight {b₁ b₂ : β} (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom
variable {G}
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] {x y : α × β} :
    (G □ H).Walk x y → G.Walk x.1 y.1
  | nil => nil
  | cons h w =>
    Or.by_cases h
      (fun hG => w.ofBoxProdLeft.cons hG.1)
      (fun hH => hH.2 ▸ w.ofBoxProdLeft)
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] {x y : α × β} :
    (G □ H).Walk x y → H.Walk x.2 y.2
  | nil => nil
  | cons h w =>
    (Or.symm h).by_cases
      (fun hH => w.ofBoxProdRight.cons hH.1)
      (fun hG => hG.2 ▸ w.ofBoxProdRight)
@[simp]
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} {b : β} :
    ∀ (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdLeft, map_cons, ofBoxProdLeft, Or.by_cases, dif_pos, ← Walk.boxProdLeft]
    · simp [ofBoxProdLeft_boxProdLeft]
    · exact ⟨h, rfl⟩
@[simp]
theorem ofBoxProdLeft_boxProdRight [DecidableEq α] [DecidableRel G.Adj] {a b₁ b₂ : α} :
    ∀ (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdRight, map_cons, ofBoxProdRight, Or.by_cases, dif_pos, ←
      Walk.boxProdRight]
    · simp [ofBoxProdLeft_boxProdRight]
    · exact ⟨h, rfl⟩
end Walk
variable {G H}
protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩
protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩
protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩
protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  haveI := hG.nonempty
  haveI := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩
protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩
protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩
@[simp]
theorem boxProd_connected : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩
instance boxProdFintypeNeighborSet (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] :
    Fintype ((G □ H).neighborSet x) :=
  Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
        Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])
theorem boxProd_neighborFinset (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) := by
  letI : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val
theorem boxProd_degree (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).degree x = G.degree x.1 + H.degree x.2 := by
  rw [degree, degree, degree, boxProd_neighborFinset, Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]
end SimpleGraph