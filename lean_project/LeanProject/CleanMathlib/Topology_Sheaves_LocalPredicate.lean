import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
universe v
noncomputable section
variable {X : TopCat.{v}}
variable (T : X → Type v)
open TopologicalSpace
open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types
namespace TopCat
structure PrelocalPredicate where
  pred : ∀ {U : Opens X}, (∀ x : U, T x) → Prop
  res : ∀ {U V : Opens X} (i : U ⟶ V) (f : ∀ x : V, T x) (_ : pred f), pred fun x : U => f (i x)
variable (X)
@[simps!]
def continuousPrelocal (T : TopCat.{v}) : PrelocalPredicate fun _ : X => T where
  pred {_} f := Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.isOpenEmbedding_of_le i.le).continuous
instance inhabitedPrelocalPredicate (T : TopCat.{v}) :
    Inhabited (PrelocalPredicate fun _ : X => T) :=
  ⟨continuousPrelocal X T⟩
variable {X}
structure LocalPredicate extends PrelocalPredicate T where
  locality :
    ∀ {U : Opens X} (f : ∀ x : U, T x)
      (_ : ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U),
        pred fun x : V => f (i x : U)), pred f
variable (X)
def continuousLocal (T : TopCat.{v}) : LocalPredicate fun _ : X => T :=
  { continuousPrelocal X T with
    locality := fun {U} f w => by
      apply continuous_iff_continuousAt.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbedding_of_le i.le).continuousAt_iff.1 w }
instance inhabitedLocalPredicate (T : TopCat.{v}) : Inhabited (LocalPredicate fun _ : X => T) :=
  ⟨continuousLocal X T⟩
variable {X T}
def PrelocalPredicate.sheafify {T : X → Type v} (P : PrelocalPredicate T) : LocalPredicate T where
  pred {U} f := ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    refine ⟨V ⊓ V', ⟨x.2, m'⟩, Opens.infLELeft _ _, ?_⟩
    convert P.res (Opens.infLERight V V') _ p
  locality {U} f w x := by
    specialize w x
    rcases w with ⟨V, m, i, p⟩
    specialize p ⟨x.1, m⟩
    rcases p with ⟨V', m', i', p'⟩
    exact ⟨V', m', i' ≫ i, p'⟩
theorem PrelocalPredicate.sheafifyOf {T : X → Type v} {P : PrelocalPredicate T} {U : Opens X}
    {f : ∀ x : U, T x} (h : P.pred f) : P.sheafify.pred f := fun x =>
  ⟨U, x.2, 𝟙 _, by convert h⟩
@[simps!]
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type v) X where
  obj U := { f : ∀ x : U.unop , T x // P.pred f }
  map {_ _} i f := ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩
namespace subpresheafToTypes
variable (P : PrelocalPredicate T)
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app _ f := f.1
open TopCat.Presheaf
theorem isSheaf (P : LocalPredicate T) : (subpresheafToTypes P.toPrelocalPredicate).IsSheaf :=
  Presheaf.isSheaf_of_isSheafUniqueGluing_types.{v} _ fun ι U sf sf_comp => by
    let sf' : ∀ i : ι, (presheafToTypes X T).obj (op (U i)) := fun i => (sf i).val
    have sf'_comp : (presheafToTypes X T).IsCompatible U sf' := fun i j =>
      congr_arg Subtype.val (sf_comp i j)
    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheafToTypes X T).existsUnique_gluing U sf' sf'_comp
    refine ⟨⟨gl, ?_⟩, ?_, ?_⟩
    · 
      apply P.locality
      rintro ⟨x, mem⟩
      choose i hi using Opens.mem_iSup.mp mem
      use U i, hi, Opens.leSupr U i
      convert (sf i).property using 1
      exact gl_spec i
    · exact fun i => Subtype.ext (gl_spec i)
    · intro gl' hgl'
      refine Subtype.ext ?_
      exact gl_uniq gl'.1 fun i => congr_arg Subtype.val (hgl' i)
end subpresheafToTypes
@[simps]
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type v) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩
def stalkToFiber (P : LocalPredicate T) (x : X) : (subsheafToTypes P).presheaf.stalk x ⟶ T x := by
  refine
    colimit.desc _
      { pt := T x
        ι :=
          { app := fun U f => ?_
            naturality := ?_ } }
  · exact f.1 ⟨x, (unop U).2⟩
  · aesop
theorem stalkToFiber_germ (P : LocalPredicate T) (U : Opens X) (x : X) (hx : x ∈ U) (f) :
    stalkToFiber P x ((subsheafToTypes P).presheaf.germ U x hx f) = f.1 ⟨x, hx⟩ := by
  simp [Presheaf.germ, stalkToFiber]
theorem stalkToFiber_surjective (P : LocalPredicate T) (x : X)
    (w : ∀ t : T x, ∃ (U : OpenNhds x) (f : ∀ y : U.1, T y) (_ : P.pred f), f ⟨x, U.2⟩ = t) :
    Function.Surjective (stalkToFiber P x) := fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheafToTypes P).presheaf.germ _ x U.2 ⟨f, h⟩
  · exact stalkToFiber_germ P U.1 x U.2 ⟨f, h⟩
theorem stalkToFiber_injective (P : LocalPredicate T) (x : X)
    (w :
      ∀ (U V : OpenNhds x) (fU : ∀ y : U.1, T y) (_ : P.pred fU) (fV : ∀ y : V.1, T y)
        (_ : P.pred fV) (_ : fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩),
        ∃ (W : OpenNhds x) (iU : W ⟶ U) (iV : W ⟶ V), ∀ w : W.1,
          fU (iU w : U.1) = fV (iV w : V.1)) :
    Function.Injective (stalkToFiber P x) := fun tU tV h => by
  let Q :
    ∃ (W : (OpenNhds x)ᵒᵖ) (s : ∀ w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ :=
    ?_
  · choose W s hW e using Q
    exact e.1.trans e.2.symm
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective'.{v, v} tU
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective'.{v, v} tV
  dsimp
  simp only [stalkToFiber, Types.Colimit.ι_desc_apply'] at h
  specialize w (unop U) (unop V) fU hU fV hV h
  rcases w with ⟨W, iU, iV, w⟩
  refine ⟨op W, fun w => fU (iU w : (unop U).1), P.res ?_ _ hU, ?_⟩
  · rcases W with ⟨W, m⟩
    exact iU
  · exact ⟨colimit_sound iU.op (Subtype.eq rfl), colimit_sound iV.op (Subtype.eq (funext w).symm)⟩
def subpresheafContinuousPrelocalIsoPresheafToTop (T : TopCat.{v}) :
    subpresheafToTypes (continuousPrelocal X T) ≅ presheafToTop X T :=
  NatIso.ofComponents fun X =>
    { hom := by rintro ⟨f, c⟩; exact ⟨f, c⟩
      inv := by rintro ⟨f, c⟩; exact ⟨f, c⟩ }
def sheafToTop (T : TopCat.{v}) : Sheaf (Type v) X :=
  ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩
end TopCat