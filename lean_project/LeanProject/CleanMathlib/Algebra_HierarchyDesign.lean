import Mathlib.Init
import Batteries.Util.LibraryNote
library_note "the algebraic hierarchy"
  def Equiv.ZEquiv (e : α ≃ β) [Z β] : by { letI := Equiv.Z e, exact α ≃Z β } := ...
  ```
## Subobjects
When a new typeclass `Z` adds new data fields,
you should also create a new `SubZ` `structure` with a `carrier` field.
This can be a lot of work; for now try to closely follow the existing examples
(e.g. `Submonoid`, `Subring`, `Subalgebra`).
We would very much like to provide some automation here, but a prerequisite will be making
all the existing APIs more uniform.
If `Z` extends `Y`, then `SubZ` should usually extend `SubY`.
When `Z` adds only new proof fields to an existing structure `Y`,
you should provide instances transferring
`Z α` to `Z (SubY α)`, like `Submonoid.toCommMonoid`.
Typically this is done using the `Function.Injective.Z` definition mentioned above.
```
instance SubY.toZ [Z α] : Z (SubY α) :=
  coe_injective.Z coe ...
```
## Morphisms and equivalences
## Category theory
For many algebraic structures, particularly ones used in representation theory, algebraic geometry,
etc., we also define "bundled" versions, which carry `category` instances.
These bundled versions are usually named by appending `Cat`,
so for example we have `AddCommGrp` as a bundled `AddCommGroup`, and `TopCommRingCat`
(which bundles together `CommRing`, `TopologicalSpace`, and `TopologicalRing`).
These bundled versions have many appealing features:
* a uniform notation for morphisms `X ⟶ Y`
* a uniform notation (and definition) for isomorphisms `X ≅ Y`
* a uniform API for subobjects, via the partial order `Subobject X`
* interoperability with unbundled structures, via coercions to `Type`
  (so if `G : AddCommGrp`, you can treat `G` as a type,
  and it automatically has an `AddCommGroup` instance)
  and lifting maps `AddCommGrp.of G`, when `G` is a type with an `AddCommGroup` instance.
If, for example you do the work of proving that a typeclass `Z` has a good notion of tensor product,
you are strongly encouraged to provide the corresponding `MonoidalCategory` instance
on a bundled version.
This ensures that the API for tensor products is complete, and enables use of general machinery.
Similarly if you prove universal properties, or adjunctions, you are encouraged to state these
using categorical language!
One disadvantage of the bundled approach is that we can only speak of morphisms between
objects living in the same type-theoretic universe.
In practice this is rarely a problem.
# Making a pull request
With so many moving parts, how do you actually go about changing the algebraic hierarchy?
We're still evolving how to handle this, but the current suggestion is:
* If you're adding a new "leaf" class, the requirements are lower,
  and an initial PR can just add whatever is immediately needed.
* A new "intermediate" class, especially low down in the hierarchy,
  needs to be careful about leaving gaps.
In a perfect world, there would be a group of simultaneous PRs that basically cover everything!
(Or at least an expectation that PRs may not be merged immediately while waiting on other
PRs that fill out the API.)
However "perfect is the enemy of good", and it would also be completely reasonable
to add a TODO list in the main module doc-string for the new class,
briefly listing the parts of the API which still need to be provided.
Hopefully this document makes it easy to assemble this list.
Another alternative to a TODO list in the doc-strings is adding Github issues.
-/
library_note "reducible non-instances"
library_note "implicit instance arguments"
library_note "lower instance priority"