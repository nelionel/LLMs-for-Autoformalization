import Mathlib.Data.Set.Basic
open Function Set
namespace Bundle
variable {B F : Type*} (E : B → Type*)
@[ext]
structure TotalSpace (F : Type*) (E : B → Type*) where
  proj : B
  snd : E proj
instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace F E) :=
  ⟨⟨default, default⟩⟩
variable {E}
@[inherit_doc]
scoped notation:max "π" F':max E':max => Bundle.TotalSpace.proj (F := F') (E := E')
abbrev TotalSpace.mk' (F : Type*) (x : B) (y : E x) : TotalSpace F E := ⟨x, y⟩
theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    .mk' F x' (cast (congr_arg E h) b) = TotalSpace.mk x b := by subst h; rfl
@[simp 1001, mfld_simps 1001]
theorem TotalSpace.mk_inj {b : B} {y y' : E b} : mk' F b y = mk' F b y' ↔ y = y' := by
  simp [TotalSpace.ext_iff]
theorem TotalSpace.mk_injective (b : B) : Injective (mk b : E b → TotalSpace F E) := fun _ _ ↦
  mk_inj.1
instance {x : B} : CoeTC (E x) (TotalSpace F E) :=
  ⟨TotalSpace.mk x⟩
theorem TotalSpace.eta (z : TotalSpace F E) : TotalSpace.mk z.proj z.2 = z := rfl
@[simp]
theorem TotalSpace.exists {p : TotalSpace F E → Prop} : (∃ x, p x) ↔ ∃ b y, p ⟨b, y⟩ :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ ↦ ⟨⟨b, y⟩, h⟩⟩
@[simp]
theorem TotalSpace.range_mk (b : B) : range ((↑) : E b → TotalSpace F E) = π F E ⁻¹' {b} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩
notation:100 E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x
@[reducible, nolint unusedArguments]
def Trivial (B : Type*) (F : Type*) : B → Type _ := fun _ => F
def TotalSpace.trivialSnd (B : Type*) (F : Type*) : TotalSpace F (Bundle.Trivial B F) → F :=
  TotalSpace.snd
@[simps (config := { attrs := [`mfld_simps] })]
def TotalSpace.toProd (B F : Type*) : (TotalSpace F fun _ : B => F) ≃ B × F where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
section Pullback
variable {B' : Type*}
def Pullback (f : B' → B) (E : B → Type*) : B' → Type _ := fun x => E (f x)
@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E
instance {f : B' → B} {x : B'} [Nonempty (E (f x))] : Nonempty ((f *ᵖ E) x) :=
  ‹Nonempty (E (f x))›
@[simp]
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace F (f *ᵖ E) → B' × TotalSpace F E :=
  fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)
@[simps (config := { attrs := [`mfld_simps] })]
def Pullback.lift (f : B' → B) : TotalSpace F (f *ᵖ E) → TotalSpace F E := fun z => ⟨f z.proj, z.2⟩
@[simp, mfld_simps]
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f (.mk' F x y) = ⟨f x, y⟩ :=
  rfl
end Pullback
end Bundle