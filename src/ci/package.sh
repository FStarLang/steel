#!/usr/bin/env bash

set -e
set -x

if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

fixpath () {
    if $is_windows ; then
        cygpath -m "$1"
    else
        echo "$1"
    fi
}

cp0=$(which gcp >/dev/null 2>&1 && echo gcp || echo cp)
cp="$cp0 --preserve=mode,timestamps"
make="$(which gmake >/dev/null 2>&1 && echo gmake || echo make)"

# make sure the package has not already been built
cd $(cd `dirname $0` && pwd)
[[ ! -e steel ]]

# download the z3 license file
if ! [[ -f LICENSE-z3.txt ]] ; then
    curl -o LICENSE-z3.txt https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt
fi

# build a F* package
if [[ -z "$FSTAR_HOME" ]] ; then
   if ! [[ -d FStar ]] ; then
       git clone https://github.com/FStarLang/FStar
   fi
   FSTAR_HOME=$(pwd)/FStar
fi
export FSTAR_HOME=$(fixpath "$FSTAR_HOME")
old_FSTAR_HOME="$FSTAR_HOME"
fstar_package_dir=$(fixpath "$FSTAR_HOME"/src/ocaml-output/fstar)
rm -rf "$fstar_package_dir"
Z3_LICENSE=$(pwd)/LICENSE-z3.txt $make -C "$FSTAR_HOME" package "$@"

# build Karamel and add it to the package
if [[ -z "$KRML_HOME" ]] ; then
    if ! [[ -d karamel ]] ; then
        git clone https://github.com/FStarLang/karamel
    fi
    KRML_HOME=$(pwd)/karamel
fi
export KRML_HOME=$(fixpath "$KRML_HOME")
$make -C "$KRML_HOME" minimal "$@"
OTHERFLAGS='--admit_smt_queries true' $make -C "$KRML_HOME"/krmllib verify-all "$@"
$cp -L $KRML_HOME/krml $fstar_package_dir/bin/krml$exe
$cp -r $KRML_HOME/krmllib $fstar_package_dir/
$cp -r $KRML_HOME/include $fstar_package_dir/
$cp -r $KRML_HOME/misc $fstar_package_dir/

# assume current directory is $STEEL_HOME/src/ci
export STEEL_HOME=$(fixpath $(cd ../.. && pwd))

# use the package to build Steel
export FSTAR_HOME="$fstar_package_dir"
OTHERFLAGS='--admit_smt_queries true' $make -C "$STEEL_HOME" "$@"
mkdir -p "$old_FSTAR_HOME"/src/.cache.boot

# install Steel into the package directory
export PREFIX="$FSTAR_HOME"
$make -C "$STEEL_HOME" install "$@"

# create the archive package
mv "$PREFIX" steel
rm -rf steel/share/fstar steel/INSTALL.md steel/README.md steel/version.txt
$cp package-README.md steel/README.md
if $is_windows ; then
  zip -r -9 steel.zip steel
else
  tar czf steel.tar.gz steel
fi
