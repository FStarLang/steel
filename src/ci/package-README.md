# The Steel separation logic system for F*

## Contents of this package

This binary package contains z3 4.8.5, F*, Karamel and Steel:

* in `bin`: the executables for z3, F* and Karamel

* in `lib/steel`:
  * the Steel F* modules of the `Steel` and `Steel.ST` namespaces
  * the Steel F* plugin, `steel.cmxs`, containing the Steel
    tactic, and the Steel and SteelC extraction to krml, is installed
    here
  * the LibSteel C library, `libsteel.a`, containing an implementation of
    what used to be the Steel part of krmllib (currently binding the
    pthreads spinlock), is installed here
  
* in `lib/steel/runtime`: the Steel OCaml runtime,
  `steel_runtime.cmxa`, necessary to compile and run Steel code
  extracted to OCaml, is installed here

* in `lib/steel/c`: the SteelC F* modules of the `Steel.C` and
  `Steel.ST.C` namespaces

* in `include/steel`: the C include files necessary to compile Steel
  code extracted to C

* in `share/steel`: `Makefile.include`, the GNU Make rules to verify
  Steel code

## Using Steel

### Writing a Makefile to verify Steel code

Steel comes with `share/steel/Makefile.include`, which contains the
GNU Make rules to call F* with the Steel include path and the Steel
plugin loaded.

1. Make sure the `bin` subdirectory is in your `PATH`.

2. Define the `STEEL_HOME` environment variable to the root directory
   of this package.

3. (Optional) In your Makefile, define the following variables with `+=` or `:=` :
   * `FSTAR_FILES`: some more F* files to verify, in addition to the
     `*.fst` and `.fsti` files of your project
   * `EXCLUDE_FILES`: some F* to skip for verification
   * `FSTAR_OPTIONS`: additional options to pass to F*. While
     `Makefile.include` is already configured to use Steel, you need
     to add more options if you need SteelC:
     * if you want to use SteelC, add `--include $STEEL_HOME/lib/steel/c`
   * `FSTAR_DEP_OPTIONS`: additional options to pass to F* to compute
     dependencies (in addition to `FSTAR_OPTIONS`), such as `--extract`
   * `FSTAR_ML_CODEGEN`: useful only if you want to extract OCaml
     code. If you want to extract a F* plugin, set this option to
     `Plugin`. Otherwise, it is set by default to `OCaml`.

4. After those variable definitions, insert `include
   $STEEL_HOME/share/steel/Makefile.include` to your Makefile.

5. In your project directory, run `make -j verify`

### Calling F* directly

If you already have an existing `Makefile` for your Steel-based project,
you now need to pass new options to your Makefile
to use Steel from this repository, as described in this section.

To call F* with Steel, pass the following options to F*:
* in all cases, `--include $STEEL_HOME/lib/steel --load_cmxs steel`
* if you want to use SteelC, add `--include $STEEL_HOME/lib/steel/c`
