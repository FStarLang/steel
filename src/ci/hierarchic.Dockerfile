# This Dockerfile should be run from the root Steel directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN . "$HOME/.cargo/env"

ADD --chown=opam:opam ./ $HOME/steel
WORKDIR $HOME/steel

# Install Karamel
ENV KRML_HOME $HOME/steel_tools/karamel
RUN mkdir -p $HOME/steel_tools && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' $HOME/steel/src/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

# Steel CI proper
ARG STEEL_NIGHTLY_CI
RUN eval $(opam env) && env STEEL_NIGHTLY_CI="$STEEL_NIGHTLY_CI" make -k -j $opamthreads -C $HOME/steel ci

ENV STEEL_HOME $HOME/steel
