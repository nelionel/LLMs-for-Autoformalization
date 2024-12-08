import Mathlib.Order.Ideal
open OrderDual
namespace Order
structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ
variable {P : Type*}
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)
theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩
namespace PFilter
section Preorder
variable [Preorder P] {x y : P} (F s t : PFilter P)
instance [Inhabited P] : Inhabited (PFilter P) := ⟨⟨default⟩⟩
instance : SetLike (PFilter P) P where
  coe F := toDual ⁻¹' F.dual.carrier
  coe_injective' := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk <| Ideal.ext h
theorem isPFilter : IsPFilter (F : Set P) := F.dual.isIdeal
protected theorem nonempty : (F : Set P).Nonempty := F.dual.nonempty
theorem directed : DirectedOn (· ≥ ·) (F : Set P) := F.dual.directed
theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h
@[trans]
theorem mem_of_mem_of_le {F G : PFilter P} (hx : x ∈ F) (hle : F ≤ G) : x ∈ G :=
  hle hx
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal (toDual p)⟩
@[simp]
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : PFilter P) ↔ toDual x ∈ I :=
  Iff.rfl
@[simp]
theorem principal_le_iff {F : PFilter P} : principal x ≤ F ↔ x ∈ F :=
  Ideal.principal_le_iff (x := toDual x)
@[simp] theorem mem_principal : x ∈ principal y ↔ y ≤ x := Iff.rfl
theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp
theorem antitone_principal : Antitone (principal : P → PFilter P) := fun _ _ =>
  principal_le_principal_iff.2
end Preorder
section OrderTop
variable [Preorder P] [OrderTop P] {F : PFilter P}
@[simp] theorem top_mem : ⊤ ∈ F := Ideal.bot_mem _
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ ≤ F.dual)
end OrderTop
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual ≤ ⊤)
section SemilatticeInf
variable [SemilatticeInf P] {x y : P} {F : PFilter P}
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F :=
  Ideal.sup_mem hx hy
@[simp]
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  Ideal.sup_mem_iff
end SemilatticeInf
section CompleteSemilatticeInf
variable [CompleteSemilatticeInf P]
theorem sInf_gc :
    GaloisConnection (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]
def infGi :
    GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  sInf_gc.toGaloisCoinsertion fun _ => sInf_le <| mem_principal.2 le_rfl
end CompleteSemilatticeInf
end PFilter
end Order