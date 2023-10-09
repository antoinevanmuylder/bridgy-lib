# POPL24, artifact 37: Agda --bridges

This artifact follows the POPL24 [author recommandations](https://popl24.sigplan.org/track/POPL-2024-artifact-evaluation#Author-Recommendations) for artifact submission.

## 0. High-level description

This artifact is an Ubuntu 20.04 virtual machine (.ova format) where [Agda --bridges](https://github.com/antoinevanmuylder/agda/tree/bridges) is installed. Agda --bridges is a proof assistant extending the [Agda](https://github.com/agda/agda) 2.6.3 proof assistant with [internal parametricity](https://lmcs.episciences.org/8651).

The virtual machine contains (see its desktop):

- The [Agda --bridges](https://github.com/antoinevanmuylder/agda/tree/bridges) repository (a fork of Agda; see `bridges` branch). Sources of Agda --bridges have been pre-compiled. The resulting binaries live in `/home/vboxuser/.local/bin/`.

- The [cubical library](https://github.com/agda/cubical) repo. An external dependency of:

- The [bridgy library](https://github.com/antoinevanmuylder/bridgy-lib), an Agda --bridges library featuring abstractions to prove internal free theorems modularly.

*Quick start.*
After having [imported the VM](https://www.virtualbox.org) into your system, load `/home/vboxuser/Desktop/bridgy-lib/Everything.agda` in emacs (C-c C-l) within the VM (some warnings may appear).
Alternatively: install Agda --bridges directly on your machine (see the [bridgy library](https://github.com/antoinevanmuylder/bridgy-lib) repo for instructions).


## 1. Download, installation, and sanity-testing

This section contains detailed installation instructions.

### Downloading and running the VM


*Downloading.* Begin by downloading the latest version of the virtual machine.

*VirtualBox.* We recommend using [VirtualBox](https://www.virtualbox.org/wiki/Downloads) v7.0.10 to import and use the virtual machine contained in this artifact. We were able to import and run this VM, using VirtualBox, on the following OSes: 
- Ubuntu desktop 20.04 and 22.04.
- Windows 10

*Importing the VM.* We follow the steps described in the VirtualBox [user manual](https://www.virtualbox.org/manual/UserManual.html#ovf-import-appliance). Go to `File > Import appliance`. Select the VM file `<...>/popl24-artifact37-VM.ova`. An "Appliance settings" window is shown. The default values should be fine; in particular:
| Option                   | Value                                         |
|--------------------------|-----------------------------------------------|
| CUP (thread)             | 2                                             |
| RAM                      | 4096MB                                        |
| MAC address policy       | Include only NAT network adapter MAC adresses |
| Import hard drive as VDI | ticked box                                    |

Click on Finish. The VM should start importing (this could take a minute).

*Running the VM.* In VirtualBox, right click popl24-artifact37-VM, and click `Start > Normal Start`.

### Once in the VM

*Misc. info.* You can change your keyboard layout in `Settings (upper right corner) > Region & Language > Input Sources`. Your linux username is `vboxuser` and your password is `password`. You can open a terminal by hitting the [Win key](https://en.wikipedia.org/wiki/Windows_key) and typing terminal.

*Directory layout.* As explained above, the three repositories of interest (`agda-fork/`, `cubical-lib/`, `bridgy-lib/`) are located in `~/Desktop`. We will omit the `~/Desktop` prefix when the context is clear.

*Kick the tires.*

- Since building a properly optimized Agda binary takes some time (~30-40min) we have already done so. To see this, run `find ~/Desktop/agda-fork/ -iname '*.o'`. This will list the generated object files. The resulting binaries sit in `~/.local/bin/`. The `agda` binary is our agda --bridges typechecker. The `agda-mode` and `size-solver` binaries can be ignored. More information about the implementation of Agda --bridges appears later in this README.

- In order to typecheck some internal parametricity proofs with agda --bridges:

  - Make sure to get our latest additions by running `git pull` in the `/Desktop/bridgy-lib/` repository.

  - Open a terminal. Type `emacs &`.
  
  - In emacs, open `bridgy-lib/Everything.agda` with the `C-x C-f` command (Agda emacs [commands](https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html)). You can typecheck the library by loading this file with `C-c C-l` (~ 1min of typechecking). This will also typecheck the necessary files from the cubical library (`cubical-lib/`). Once the library is typechecked you should see colored syntax and some warnings in the buffer below. To erase the results of typechecking run `make clean` in  `bridgy-lib/` and in `cubical-lib/`.
  
  - You can consult our examples of internal free theorems in `bridgy-lib/Bridgy/Examples/` (The "Jump to file" emacs shortcut is `M-.`).
  
In the rest of this section we provide a table of approximate compiling/typechecking times and optional "kick the tires" objectives.

### Compiling/typechecking times.

Within the VM, when 2048MB of memory and 2CPU threads are allocated, on a 3years old 16GB RAM/8cores work laptop:

| X compiles/typechecks | Y                            | in ... | comment                                              |
|-----------------------|------------------------------|--------|------------------------------------------------------|
| ghc 9.0.2             | Agda dependencies            | 9 min  | not a --fast install (i.e. optimized binary)         |
| ghc 9.0.2             | Agda sources                 | 29min  | not a --fast install (i.e. optimized binary)         |
| ghc 9.0.2             | Agda sources                 | ~6min  | --fast install                                       |
| agda --bridges        | cubical lib (README.agda)    | 41min  | with the original `agda` binary (properly optimized) |
| agda --bridges        | bridgy-lib (Everything.agda) | ~1min  | with the original `agda` binary (properly optimized) |

  
### (Optional) Typechecking the entire cubical library with Agda --bridges

This can take quite a while (see above table) but can be stopped at any time (abort typechecking emacs shortcut: `C-c C-x C-a`).

- Go the cubical library repo `cd ~/cubical-lib/`

- Type `stack exec -- make gen-everythings`

- With emacs, load the file `~/cubical-lib/Cubical/README.agda`
  
### (Optional) Re-compiling the Agda --bridges implementation

- Before re-compiling agda --bridges from source, we remark that a copy of the original optimized binaries appears in `~/Desktop/save-bins/`.

- Go to `agda-fork/`. To delete the build products, run `stack clean`. Alternatively modifying the implementation of agda --bridges (typically files like `agda-fork/src/full/Agda/TypeChecking/<...>.hs`) will trigger recompilation upon next compile command.

- Run `stack install --fast` or `stack install`. The compilation times appear in the above table.

### (Optional) Make tags in agda --bridges code base.

- A TAGS file has been pre-generated: `agda-fork/src/full/TAGS`.

- In case of a problem see [here](https://github.com/antoinevanmuylder/bridgy-lib/blob/main/INSTALL.org).


## 2. List of claims

We list the claims made in the paper along with the associated fragments of the artifact and corresponding evaluation instructions (see section 3).

Some remarks:


- This correspondance is using the first submitted version of our paper, not the camera-ready version.

- We acknowledge that the Agda --bridges implementation is not in an entirely satisfactory state (although a functioning state; see later) . It could use some refactoring, bug fixing, documentation, ... . The Agda code base is not small and thus further improving our implementation takes time.

- While looking at the implementation of Agda --bridges, it can be useful to keep an eye on the [Cavallo-Harper](https://lmcs.episciences.org/8651) paper and the rules listed there. The main differences between CH and agda --bridges are
  1. We have (semi)freshness typechecking constraints, while CH have a context restriction operation.
  2. We have a different logic of face constraints (extending the face logic of agda --cubical).

- In accordance with the artifact recommandations, we follow the paper structure to list our claims.



### (1) introduction

| line | claim                                                                                     | place in the artifact                          | evaluation                                 |
|------|-------------------------------------------------------------------------------------------|------------------------------------------------|--------------------------------------------|
| 114  | Agda --bridges implements the parametricity primitives of CH                              | lots                                           | see 3.1 and below                          |
| 116  | Agda --bridges succesfully compiles the full Agda --cubical standard library              | `cubical-lib/`                                 | see sec.1                                  |
| 118  | We  benefit from strong extensionality principles like the univalence and funext theorems | e.g. `bridgy-lib/Bridgy/Core/GelExamples.agda` | relativity uses univalence, e.g.           |
| 121  | We prove relativity                                                                       | `bridgy-lib/Bridgy/Core/GelExamples.agda`      | this file typechecks. See also 3.4         |
| 137  | Our param theorem. (Note: see section 3.2.2 and not 4.1)                                  | `bridgy-lib/Bridgy/ROTT/Param.agda`            | See `bridgy-lib/Bridgy/Examples`           |
| 140  | "are one-liner invocations of param"                                                      | e.g. `bridgy-lib/Bridgy/Examples/Church.agda`  | See `param` call                           |
| 152  | We contribute a DSL named ROTT                                                            | `bridgy-lib/Bridgy/ROTT/`                      | See `Judgments.agda` and `Rules.agda` e.g. |

### (2) the internal parametricity of agda --bridges

| line      | claim                                                                          | place in the artifact                          | evaluation                                             |
|-----------|--------------------------------------------------------------------------------|------------------------------------------------|--------------------------------------------------------|
| 390       | We implemented the interval `BI`                                               | see 3.1                                        | see 3.1                                                |
| 405       | "[tick] has the effect of raising a constraint", tick app rule                 | `TC/Rules/Application.hs` (l876).              | see 3.2                                                |
| 424       | We implemented all the rules of the BridgeP type                               | see 3.1                                        | e.g. `/bridgy-lib/Bridgy/Core/BridgeExamples.agda`     |
| 450 , 286 | We implemented extent and all of its rules (incl. beta). We proved extentEquiv | see 3.1                                        | see 3.3                                                |
| 486       | We implemented a capturing-under-semifreshness algorithm                       | see 3.1                                        | see 3.3                                                |
| 533       | We implemented Gel and all of its rules (incl. eta). We proved relativity      | see 3.1                                        | see 3.4                                                |
| 579       | We can prove other relational extensionality principles                        | `bridgy-lib/Bridgy/Core/`                      | see 3.5                                                |
| 624       | We can prove fthm (the version with 2 list arguments)                          | `bridgy-lib/Bridgy/Examples/AListFreeThm.agda` | see `fthm`, and the `param call` (we already use ROTT) |
| 632       | "this [SRP] discipline simplifies the proofs a lot                             | `bridgy-lib/Bridgy/Examples/LowLevel.agda`     | see `lowChurchBool` theorem                            |


### (3) the observational parametricity of agda --bridges


| line | claim                                  | place in the artifact                      | evaluation                                                                |
|------|----------------------------------------|--------------------------------------------|---------------------------------------------------------------------------|
| 679  | SRP by hand can be cumbersome          | `bridgy-lib/Bridgy/Examples/LowLevel.agda` | see `lowChurchBool` theorem                                               |
| 768  | Implementation of NRGs, dNRGs and more | `bridgy-lib/Bridgy/ROTT/Judgments.agda`    | see `NRGraph`, `NRelator`, `DispNRG`, `TermDNRG`                          |
| 828  | Examples of (d)NRGs                    | `bridgy-lib/Bridgy/ROTT/Rules.agda`        | see "type formers" section and below                                      |
| 860  | internal-observational `param`         | `bridgy-lib/Bridgy/ROTT/Param.agda`        | /                                                                         |
| 875  | "The other rules of ROTT"              | `bridgy-lib/Bridgy/ROTT/Rules.agda`        | for the path dNRG, see `bridgy-lib/Bridgy/Experimental/ChurchCircle.agda` |


### (4) internal observational parametricity applied

The examples shown in this section of the paper can be found in `bridgy-lib/Bridgy/Examples/`:

- `fthm` (or rather the `gen-fthm` of the introduction (l85 in the paper)) is found in `AListFreeThm.agda`

- Specific Church encodings can be found in `Church.agda`. The scheme of Church encodings of 4.2 (l939 in paper) is the `genericChurch` theorem of file `GenericChurch.agda`.

- The system F result of section 4.3 (l995 in paper) can be found in `SystemF.agda` (warnings may appear upon typechecking). Reynolds' theorem is the `sysf-param` theorem. An instance of this theorem appears below.

### (5) about the implementation, transp and hcomp


Claim (l1034 of paper): "We have finished the implementation of the bridge-enhanced versions of transp and hcomp..."
Evaluation: see 3.6 and 3.1.



## 3. Evaluation instructions

## 3.1 Where are things in the Agda --bridges code base

- A diff between Agda 2.6.3 and agda --bridges can be obtained using the following commands in `agda-fork/`:

  ```bash
  git checkout release-2.6.3
  git checkout bridges
  git diff --shortstat release-2.6.3 bridges    #line count
  git diff release-2.6.3 bridges                #total diff
  git diff release-2.6.3 bridges -- file.hs     #just on file.hs
  ```

- A list of all the primitives we implemented can be found in `/bridgy-lib/Bridgy/Core/BridgePrims.agda`.

- This table describes where to find (the most important) code bits of Agda --bridges. `TC` stands for `~/Desktop/agda-fork/src/full/Agda/TypeChecking/`. We only speak about the agda --bridges primitives naturally.

  | What?                                                    | Where?                                                                                                |
  |----------------------------------------------------------|-------------------------------------------------------------------------------------------------------|
  | Types of primitives                                      | either `TC/Primitive/Bridges.hs` or `TC/Rules/Builtin.hs`                                             |
  | Reduction rules                                          | `TC/Primitive/Bridges.hs`                                                                             |
  | eta rules (typed-directed comparison procedures)         | `TC/Conversion.hs`                                                                                    |
  | Other rules (e.g. bridge elim)                           | `TC/Rules/`                                                                                           |
  |----------------------------------------------------------|-------------------------------------------------------------------------------------------------------|
  | Affine behaviour                                         | `TC/Lock.hs`, `TC/Rules/Application.hs` (l876), `TC/Primitive/Bridges.hs`                             |
  |----------------------------------------------------------|-------------------------------------------------------------------------------------------------------|
  | Face constraints: comparing, computing                   | `TC/Primitive/Bridges.hs`, `TC/Conversion.hs`                                                         |
  | Pattern matching for (mixed) partial elements            | `TC/CompiledClaused/Match.hs`, `TC/Coverage/`, `TC/Rules/Def.hs`,  `TC/Rules/LHS.hs`, `TC/Rules/LHS/` |
  |----------------------------------------------------------|-------------------------------------------------------------------------------------------------------|
  | hcomp/transp: reduction clauses                          | `TC/Primitive/Cubical.hs`, `TC/Primitive/Bridges.hs`                                                  |
  | hcomp/transp: helpers for data/record types              | `TC/Rules/Data.hs`, `TC/Rules/Record.hs`                                                              |
  | hcomp/transp: Computational typechecking side conditions | `TC/Rules/Application.hs`                                                                             |

## 3.2 About tick annotations, substructurality ("affineness")

From `TC/Rules/Application.hs` (l876):
```haskell
let c = Just $ Abs "t" (CheckLockedVars (Var 0 []) (raise 1 sFun) (raise 1 $ Arg info' u) (raise 1 binterval))
```

Intuitively, what gets checked when raising the above typechecking constraint `c` is the premisse "fresh f,r" of the tick-app rule (line 409 in paper).
More concretly, in the implementation, the following function (checking freshness of free variables) gets called when constraints like `c` are being investigated by the typechecker :`TC/Lock.hs > isTimeless'`.

To see that this "fresh" premisse is correctly implemented on an example, uncomment `no-destr-bdg` in `bridgy-lib/Bridgy/Core/BridgeExamples.agda and try to typecheck. This will result in an error as expected.

## 3.3 extent

- To see that extent works properly (up to a minor normalisation bug which does not affect our examples), typecheck `/bridgy-lib/Bridgy/Core/BridgePrims.agda`,  `/bridgy-lib/Bridgy/Core/ExtentExamples.agda`. The latter contains the extentEquiv  theorem (l453 of the paper) under the name ΠvsBridgeP.

- The extent primitive is mostly implemented here: `TC/Primitive/Bridges.hs > primExtent'`. The latter program specificies the type of extent (`TC/Primitive/Bridges.hs > extentType`) and how it weak-head-normal reduces (beta rule). In particular capturing occurs (see where function `captureIn`) under a semi-freshness constraint (see `semiFreshForFvars` call).

## 3.4 Gel

- To see that Gel works properly, typecheck `bridgy-lib/Bridgy/Core/BridgePrims.agda`,  `bridgy-lib/Bridgy/Core/GelExamples.agda`. The latter contains the relativity theorem. The diagram linked in one of the lemmas of relativity can be found [here](https://q.uiver.app/?q=WzAsMTAsWzAsMSwiXFxtYXRocm17QmRnfV9BIFxcOyBJXzBeey0xfUlfMChhXzApICxcXDsgSV8xXnstMX1JXzEoYV8xKSJdLFswLDMsIlxcbWF0aHJte0JkZ31fQSBhXzAgXFw6IGFfMSJdLFs0LDEsIlxcbWF0aHJte0JkZ31fQiBcXDsgSV8wSV8wXnstMX1JXzAoYV8wKSAsXFw7IElfMUlfMV57LTF9SV8xKGFfMSkiXSxbNCwzLCJcXG1hdGhybXtCZGd9X0IgSV8wYV8wICxcXDogSV8xYV8xIl0sWzAsNCwiXFxtYXRocm17Ynl9XFw6SV57LTF9SSBcXHRvIGlkIl0sWzQsNCwiXFxtYXRocm17Ynl9XFw6SUleey0xfSBcXHRvIGlkIl0sWzIsMl0sWzEsMF0sWzIsMCwiXFxtYXRocm17VE9QfVxcLGlcXCxqXFwsPVxcLHVhIChIIChcXG1hdGhybXtyZXRFcX1cXCxJXFwsYVxcLChcXHNpbSBqXFxsYW5kIGkpKSAoalxcbGFuZCBpKSJdLFsyLDQsIlxcbWF0aHJte0JPVH1cXCxpXFwsalxcLD1cXCx1YSAoSCAoXFxtYXRocm17cmV0RXF9XFwsSVxcLGFcXCwoXFxzaW0galxcbG9yIGkpKSAoalxcbG9yIGkpIl0sWzAsMSwiXFxtYXRocm17YVN1YnN0fVxcLGFfMCBcXCwgYV8xIiwyXSxbMiwzLCJcXG1hdGhybXtiU3Vic3R9XFwsSV8wYl8wICxcXDogSV8xYl8xIiwwLHsiY3VydmUiOi0yfV0sWzEsMywiSCBhXzAgYV8xIiwyXSxbMCwyLCJIXFw6SV8wXnstMX1JXzAoYV8wKSAsXFw7IElfMV57LTF9SV8xKGFfMSkiXSxbMiwzLCJcXHRpbGRle1xcbWF0aHJte2JTdWJzdH19IiwyLHsiY3VydmUiOjJ9XSxbMSwyXSxbMTEsMTQsIiIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMTMsMTUsIlxcbWF0aHJte1RPUH0iLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzE1LDEyLCJcXG1hdGhybXtCT1R9IiwyLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==).

- On the implementation side, Gel and its intro/elim terms gel/ungel are defined in `TC/Primitive/Bridges.hs`. The eta-rule of Gel is similar to extent-beta as it also makes use of capturing (under a semifreshness constraint). See `TC/Conversion.hs > compareGelTm`.



## 3.5 Other relational extensionality principles

- BridgePvsBridgeP, PathPvsBridgeP, ΣvsBridgeP, ×vsBridgeP : `bridgy-lib/Bridgy/Core/BridgeExamples.agda`

- for equivalences (pequivBridgeP) : `bridgy-lib/Bridgy/Core/GelExamples.agda`

- ListvsBridgeP : `bridgy-lib/Bridgy/Core/List.agda`

## 3.6 About transp and hcomp

Some [background](https://agda.readthedocs.io/en/v2.6.3/language/cubical.html) on --cubical.

Adapting transport and homogeneous composition to the bridges setting required the definition of quite a number of primitives.
These primitives are summarized in `bridgy-lib/Bridgy/Core/BridgePrims.agda`. They are the ones appearing strictly after the `prim^ungel` primitive.
Instead of modifying the --cubical `hcomp` primitive directly we added a new separate (but related) primitive called `mhocom` in the paper or `primMHComp` in the implementation.
We did not need to do that for transport: for this --cubical primitive we simply added the appropriate definitional equations. Here are the types of the transport/hcomp primitive existing in Agda --bridges.

```agda
primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1                -- a.k.a. transp

primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A            -- a.k.a. hcomp
primMHComp : ∀ {ℓ} {A : Type ℓ} {ζ : MCstr} (u : ∀ i → MPartial ζ A) (u0 : A) → A      -- a.k.a. mhocom
```

Note that the reduction rules of `transp` generate terms containing `mhocom`, and conversely. That is to say, their equational theory is defined by mutual induction.

Overall we have relatively good confidence in the soundness of our implementation of the mhocom/transp reduction behaviour w.r.t. the CH theory for two reasons.

- Agda --bridges typechecks the entire cubical-library (see sec. 1). When the --bridges flag is active, an `hcomp` call reduces to a `mhocom` call instead (see `TC/Primitive/Cubical.hs > primHComp'`), and reduction rules for `mhocom` are used (we wrote those) instead of the ones for `hcomp` (that the --cubical developers wrote). This indicates that `mhocom` behaves as expected, at least in the case where its ζ and u argument come from a --cubical invocation of hcomp, i.e. contain trivial bridge information.

- Agda --bridges typechecks the bridgy library. Each time a `transp` reduces at a line of types like `BridgeP/Gel/mhocom`, the "bridge-ful" fragment of the reduction clauses we wrote for `transp` and, in turn, `mhocom` get called. In our view, it is unlikely (though not impossible) that these reduction clauses are unsound since typechecking errors would occur quite quickly otherwise. Such errors have occured in the past and we fixed them. What is more possible is a lack of completeness w.r.t the reduction behaviour of transp/mhocom in CH. In other words it could be that some definitional equalities involving transp/hcomp are obtainable in CH but not in Agda --bridges. Experimenting with Agda --bridges on more complex examples of internal free theorems (future work) could reveal such defects.


We now explain our implementation of transp/mhocom in more details.
Before explaining where to find the equations for `primTransp` and `primMHComp` we explain the `MCstr` and `MPartial` constituents appearing in the type of `mhocom`.

### Mixed face constraints (MCstr)

In the --cubical case, the `hcomp` primitive is used to modify a term (u0 : A) that contains path variables `i,j,k,...` into a term `hcomp {l} {A} {φ} u u0` that computes more pleasingly.
Specifically, contrary to `u0`, the latter term is definitionally equal to `u (i1)` when the φ constraint is found satifiable.
The φ face constraint restricts what values `i,j,k,...` can possibly take. Since agda --cubical uses a rich path interval structure (De Morgan), specifying such a constraint can simply be done by stating
a single equation like
```agda
i ∧ ((~ j) ∨ k) = i1
```
This is why path face constraints can simply be specified as terms φ : I. For instance, to assert the above face constraint on `i,j,k` we would use `φ := i ∧ ((~ j) ∨ k)`.
(φ could denote the LHS of the above equation, e.g.)


In the --bridges case, the `mhocom` primitive ought to be used for modifying a term (u0 : A) that can contain path variables `i,j,k,...` *and bridge variables* `x,y,z,...` into a term `mhocom {l} {A} {ζ} u u0` that computes more pleasingly.
Again the latter term should be definitionally equal to `u (i1)` when the `ζ` constraint is found satisfiable (contrary to u0).
The ζ face constraint restricts what values `i,j,k,...` *and also* `x,y,z` can possibly take.
Since the bridge interval does not admit any operations besides having endpoints `bi0, bi1` (so no connections ∧, ∨ e.g.) specifying such a constraint ζ can *not* be done straightforwardly.

To remain logically sound w.r.t. to a denotational model (specifically: `psh (DeMorgan-cube × Affine-cube)`) we pin pointed the following definition:

1. First, we define what a "pure" bridge constraint is, i.e. a constraint like ζ saying nothing about path variables. See `BCstr` and module `BCstrPrims` in `bridgy-lib/Bridgy/Core/BridgePrims.agda`. Such a bridge constraint ψ : BCstr can be unsatisfiable (see `bno`), OR vaccuous (see `byes`) OR a disjunction of atomic assertions like `x = bi1` or `x = bi0`. Examples of `ψ : BCstr` can be found in `bridgy-lib/Bridgy/Test/CstrExamples.agda`.

2. Second we define the type of mixed face constraints `ζ : MCstr`. Intuitively, ζ can be a union (see `_m∨_`) of a bridge constraint `ψ:BCstr` and of a path constraint `φ:I`, OR a vaccuous mixed constraint (see `myes`), OR a false one (see `mno`). This is what the quotient on line 1074 of our submission tells. The implementation of the `_m∨_` "constructor" of MCstr can be found here: `TC/Primitive/Bridges.hs > primMkmc'`. Non trivial mixed constraints `ζ` can be specified using the `_∨∨_ : MCstr -> MCstr -> MCstr` primitive which is implemented here `TC/Primitive/Bridges.hs > primMixedOr'`.

3. In --cubical there exists a primitive type former called `IsOne` to assert truth for path constraints. Its only constructor is `itIsOne : IsOne i1`. Hence the only way for a path constraint φ to be satisfiable is for it to reduce to `i1` (in a certain context). Similarly, Agda --bridges features an analogous primitive predicate about *mixed* constraints, called `MHolds`. Its only constructor is `MitHolds : MHolds myes`. Hence the only way for a mixed constraint ζ to be satisfiable is for it to reduce to `myes`.

Related Agda --bridges primitives:
```agda
primReflectMCstr : ∀ {φ : I} -> .(MHolds (φ m∨ bno)) -> IsOne φ
primPrsvMCstr : ∀ {φ : I} → .(IsOne φ) → MHolds (φ m∨ bno)
primEmbd : I → MCstr
```


### Mixed partial elements (MPartial)


The next constituent of `mhocom` we discuss is the `MPartial : ∀ {l} -> MCstr -> Type l -> SSet l` primitive type former. It is a --bridges counterpart of the `Partial` type former of --cubical. Basically, (MPartial ζ A) is defined as a function type (MHolds ζ → A) (see `TC/Primitive/Bridges.hs > primMPartial'`). In other words, elements of MPartial ζ A are terms of A defined only when the ζ constraint holds.

As is the case for `Partial φ A` elements, elements of `MPartial ζ A` can be defined by pattern matching (see e.g. `mpart3` in `bridgy-lib/Bridgy/Test/CstrExamples.agda`).
See 3.1 for the relevant files in the implementation. When the user proposes a definition of an `u : MPartial ζ A` by pattern matching, the Agda --bridges typechecker verifies 2 facts:

1. Coverage: the user did not forget any cases, i.e. the mixed union (_∨∨_) of all constraints found in the LHS of pattern matching clauses equals ζ.
2. Coherence: Clauses agree where they overlap.

In practice non-trivial mixed partial elements are not typically written by the user, and rather occur in the outputs of `transp/mhocom` reductions.


### Other auxiliary primitives for mhocom

There are other Agda--bridges primitives that are useful for specifying how transport and mhocom reduce, but that we don't discuss here.
`MPartialP`, `mholdsEmpty`, `MHolds1`, `MHolds2`, `prim^mpor`.

Additionally, the two following primitives implement the ∀ operation on face constraints from the Cavallo-Harper paper:

```agda
primAllMCstr : ((@tick x : BI) → MCstr) → MCstr
primAllMCstrCounit : {absζ : ((@tick x : BI) → MCstr)} → .(oall : MHolds (primAllMCstr absζ)) → (@tick x : BI) → MHolds (absζ x)
```

### transp and mhocom reduction rules


The `transp` and `mhocom` primitives reduce based on the exact shape of their type(line) argument `A` (see above).
Several of these rules use capturing and some use the above auxiliary primitives.

*Transp.* (overall reduction behaviour: `TC/Primitive/Cubical.hs > primTrans'`)


| A : I -> Type                                                 | implementation                             |
|---------------------------------------------------------------|--------------------------------------------|
| line of BridgeP types                                         | `TC/Primitive/Bridges.hs > transpBridgeP`. |
| line of Gel types                                             | `TC/Primitive/Bridges.hs > transpGel`.     |
| line of types of the form`hcomp {A = Type} {φ} u (u0 : Type)` | `TC/Primitive/Cubical.hs`                  |

Remark wrt last kind of line:
We could not find any well typed equation for `transp` at lines of types of the more general form `mhocom {A} {ζ} u (u0 : Type)` so the present reduction rule fires only if ζ is a (embedded) path constraint. We have not needed such a more general equation (⋆).



*Mhocom.* (overall reduction behaviour: `TC/Primitive/Bridges.hs > primMHComp'`)

The following table lists the reduction clauses available to compute a term `mhocom {l} {A} {ζ} u u0`.


| A : Type                     | implementation                                                                            | comment                                                |
|------------------------------|-------------------------------------------------------------------------------------------|--------------------------------------------------------|
| Pi                           | `TC/Primitive/Bridges.hs > mhcompPi`                                                      |                                                        |
| Glue                         | `TC/Primitive/Bridges.hs > mhcompGlue`                                                    |                                                        |
| Gel                          | `TC/Primitive/Bridges.hs > mhcompGel`                                                     |                                                        |
| (mhocom {A = Type} {ζ = ζ'}) | `TC/Primitive/Bridges.hs > mhcompMixHCompU`                                               | fires only if ζ' is a path constraint (a bit like (⋆)) |
| PathP                        | `TC/Primitive/Bridges.hs > mhcompPathP`                                                   |                                                        |
| BridgeP                      | `TC/Primitive/Bridges.hs > mhcompBridgeP`                                                 |                                                        |
| Id Swan type                 | `TC/Primitive/Bridges.hs > mhcompBridgeP`                                                 | only if ζ is a path constraint (a bit like (⋆))        |
| record type                  | `TC/Primitive/Bridges.hs > primMHComp'` and `TC/Rules/Record.hs > defineMixHCompR`        |                                                        |
| data type                    | `TC/Primitive/Bridges.hs > mhcompData`  and `TC/Rules/Data.hs > defineMixHCompForFields0` | not indexed/HIT.                                       |




Additionally, typechecking side conditions for `transp` and `mhocom` appear in `TC/Rules/Application.hs`.
For instance, `mhocom {l} {A} {ζ} u u0` is rejected if `u (i0)` is not definitionally equal to u0.
