# This Dockerfile should be run from the root Steel directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

ARG opamthreads=24

ADD --chown=opam:opam ./ steel/

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    wget \
    pkg-config \
    jq \
    && \
    git clone --branch $(jq -c -r '.RepoVersions.fstar' steel/src/ci/config.json || echo master) https://github.com/FStarLang/FStar $FSTAR_HOME && \
    eval $(opam env) && \
    opam depext conf-gmp z3.4.8.5-1 conf-m4 && \
    opam install --deps-only $FSTAR_HOME/fstar.opam && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' steel/src/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

# FIXME: The recent changes to MLish and bootstrapping mean that we must
# not try to check prims.fst or the rest of ulib in --MLish mode, since
# some files fail to do so. This will happen when trying to extract the
# files in src/syntax_extension, as there are no checked files for them.
# So, call the F* makefile to bootstrap F* and generate the files. This
# is probably only a bandaid... but I'm not sure what the best thing to
# do is.
RUN eval $(opam env) && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads bootstrap

# Steel CI proper
ARG STEEL_NIGHTLY_CI
ARG OTHERFLAGS=--use_hints
RUN eval $(opam env) && . $HOME/.cargo/env && env STEEL_NIGHTLY_CI="$STEEL_NIGHTLY_CI" make -k -j $opamthreads -C steel/src ci

ENV STEEL_HOME $HOME/steel
