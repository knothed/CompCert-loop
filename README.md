# CompCert-loop

A fork of the formally-verified C compiler, extending it with some loop optimizations.
This is the accompanying development to our paper [Combining Small-Step and Big-Step Semantics to Verify Loop Transformations](todo).

Build and install CompCert-loop using `./configure x86_64-linux && make && sudo make install`. It may take some time, especially on the file `CminLoopRemoveSkips.v`.
We tested our development with `coq 8.17.1` and `OCaml 4.14.1`.

To compile a file, use `ccomp file.c -floop`. Add the `-dcminor` flag to see the intermediate states before (`.cm.0`), during (`.cml.0/1/2/3`) and after (`.cm.1`) loop optimizations on Cminor/CminLoop.

---

A nice use-case of loop unrolling is the following. This code calculates `10!`:
```c
int main() {
  int x=1;
  for (int i=1; i<11; i++)
    x = x*i;
  return x;
}
```
Compiling it with `-floop` and `-S` to show the resulting assembly, we see that the loop has been removed entirely and the value of `10!` has been calculated by the compiler:
```asm
movl $3628800, %eax
```

After our loop unrolling pass, the code looks like this:
```c
int x=1; int i=1;
x = x*i;
i++;
x = x*i;
i++;
...
x = x*i;
i++;
```
CompCert's existing constant propagation pass then calculates the final value of `x` and removes all of the above code.

## Loop Optimizations

We have implemented and verified the following loop transformations:

- **Full Loop Unrolling**: unroll the body of a loop with integer literal bounds. (Maximum 16 iterations, comparison must be `<` and latch must be of the form `i++`).
  ```c
  for (int i=1; i<12; i++) {
    printf("%d", i);
  }
  ```
- **Loop Inversion**: move the loop condition behind the loop body, and put the condition around the whole loop. Currently, the code requires a weird form to be detected by our optimization - the loop body must be integrated insde the latch, as seen below. This can easily be fixed in the future.
  ```c
  for (int j=1; j<10;
    printf("%d", j),
    j++
  );
  ```

- **While-True Simplification**: eliminate the body of a never-ending while-true loop that never calls any function nor emits any other kind of visible event.
  ```c
  while (1) {
    i = i+1;
  }
  ```

- **Loop Unswitching**: hoist an independent if-statement out of a loop. While verified, this transformation cannot be applied to real code yet because CompCert compiles loops into a form that is not supported by this transformation. We should have tested it before proving...

- **Skip / Dummy Removal**: helper transformations to remove unnecessary `Sskip` statements to give the Cminor code a simpler form so our transformations can better detect it.


## Organization of Our Changes:

* Semantics (in `common/`):
    * `Semantics.v` introduces behavioral semantics, its properties and preservation theorems.
    * `SemanticsSmallBig.v` puts small-step and big-step semantics into the behavioral framework.
    * `Tracex.v` contains our general (finite+infinite) trace, and `Foreverx.v` introduces the general-trace divergence judgment for small-step semantics and shows a form of equivalence between `forever` and `foreverx`.
    * `Determinacy.v` contains useful lemmas for reasoning about determinate small-step executions.
* Compiler (in `driver/`):
    * `CompilerSmallstep.v` is the original small-step compiler pipeline, but split up into two parts: `C -> Cminor` and `Cminor -> Asm`.
    * `Compiler.v` establishes our new compilation pipeline: it integrates CompilerSmallstep, executes the `Cminor <-> CminLoop` transformation and performs all loop optimizations on CminLoop. It establishes the top-level preservation theorems. It also handles linking.
    * `Complements.v` proves the same top-level correctness consequences as before using our new compiler pipeline.
    * We also adapted the big-step semantics of `cfrontend/Cstrategy.v` to fit it into our behavioral framework, thereby strengthening `Theorem bigstep_cstrategy_preservation` (assuming the adapted big-step semantics is sound w.r.t. the old one, which we did not prove).
* CminLoop (in `backend/`):
    * `CminLoop.v` introduces CminLoop, a version of Cminor that does not contain goto statements.
    * `CminLoopBigSmallEquiv.v` establishes equivalence between small-step and big-step CminLoop by proving soundness and completeness.
    * `CminLoopOldDivergence.v` shows a form of equivalence between the old and new notions of big-step divergence. This is not required for the development.
    * `DropGotos.v` converts between Cminor and CminLoop in a small-step fashion.
* Loop Transformations (in `backend/`):
    * `CminLoopInvert.v`, `CminLoopUnroll.v`, `CminLoopUnswitching.v` and `CminLoopWhileTrue.v` contain the transformations as described above.
    * `CminLoopRemoveSkips.v` and `CminLoopRemoveDummys.v` remove skip and dummy statements. Dummy statements are a technicality required for coinductively verifying transformations that *remove* statements: `(Sseq Sskip stmt) --> stmt` cannot be verified, but `(Sseq Sskip stmt) --> Sdummy stmt` can be.
    * `CminLoopRepeatTransform.v` enables us to repeat transformations multiple times in a row (in particular, we use it for thoroughly removing skip and dummy statements).
    * `CminLoopTransfCommon.v` contains some definitions, lemmas and tactics that help in proving various different loop transformations.

In total, our development added and modified around 8.000 lines of Rocq code.


-----

*This is a fork of CompCert. The original README of CompCert is below:*

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
