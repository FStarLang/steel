# Developer's guide

This section is useful only if you want to contribute to Steel
or SteelC code.

In all cases (user or developer), please first read `README.md`

## Source layout

* In `src/c`: The handwritten LibSteel library for C (currently
  binding the pthreads spinlock)
* In `src/extraction`: The krml extraction rules for Steel and
  SteelC. This F* code typechecks against the F* sources.
* In `src/ocaml/runtime`: The handwritten Steel runtime library for
  OCaml. This OCaml code typechecks and compiles against the
  `fstar.lib` package.
* In `src/ocaml/plugin/generated`: A snapshot of the generated OCaml
  code for the Steel plugin, containing the extracted implementations
  of the Steel tactic and the Steel and SteelC extraction
  to krml.
* In `src/proofs/steelc`: The F* correctness proofs of the SteelC
  library, i.e. the `*.fst` implementations of the
  `lib/steel/c/Steel.ST.C.*.fsti` interfaces. Those files are not
  necessary for the end-user, and they take a large amount of time and
  memory to verify.

## Building

Running `make` will verify the Steel files, build the plugin, and use
the plugin to verify the Steel library, all in proper order.

However, this rule will not reverify the proofs from `src/proofs`,
which basically have no impact on the user code. These proofs take
very long time and high amounts of memory to verify.

## Testing

`share/steel` contains all examples and tests. You can run `make -j -C
share/steel` to verify and test them. This rule will work whether you have
Karamel or not. If you have Karamel, then this rule will also extract
and compile (and sometimes run) C extraction examples. Alternatively,
you can run `make -j test` from the Steel root directory, which will
build Steel beforehand.

If you have Docker, you can run `docker build -f
src/ci/opam.Dockerfile .` to test the opam installation of Steel
(including all dependencies.) This will also verify all examples and
tests, by moving them outside of the Steel directory hierarchy
beforehand, to make sure that the location of those examples does not
need to depend on the location of Steel.

Finally, you can run `make -j -C src ci` to re-extract, recompile and
re-test everything. This rule also checks that the re-extracted
snapshot is no newer than the current snapshot. If the
`STEEL_NIGHTLY_CI` environment variable is set to a nonempty value,
then this rule also includes the proofs from `src/proofs`, so it will
take time and memory. If you have Docker, you can run the `ci` rule
with `docker build -f src/ci/ci.Dockerfile .` which will also
install all dependencies automatically.

TODO: add GitHub Actions workflows for continuous integration
