# This Dockerfile should be run from the root Steel directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

# CI dependencies for the Wasm11 test: node.js
# The sed call is a workaround for these upstream issues... sigh.
# https://github.com/nodesource/distributions/issues/1576
# https://github.com/nodesource/distributions/issues/1593
# Remove when they are solved
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sed 's,https://deb.nodesource.com,http://deb.nodesource.com,' | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

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
ARG OTHERFLAGS=--use_hints
RUN eval $(opam env) && env STEEL_NIGHTLY_CI="$STEEL_NIGHTLY_CI" make -k -j $opamthreads -C $HOME/steel/src ci

ENV STEEL_HOME $HOME/steel
