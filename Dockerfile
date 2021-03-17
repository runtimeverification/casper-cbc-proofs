FROM ubuntu:bionic

RUN    apt-get update               \
    && apt-get upgrade --yes        \
    && apt-get install --yes        \
                    bubblewrap      \
                    build-essential \
                    curl            \
                    git             \
                    m4              \
                    ocaml           \
                    rsync           \
                    unzip           \
                    wget            \
                    python3         \
                    python3-pip     \
                    graphviz

ENV OPAM_VERSION="2.0.7"

ADD --chown=root:root https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/opam-${OPAM_VERSION}-x86_64-linux /usr/bin/opam
RUN chmod ugo+x /usr/bin/opam

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

# From: https://github.com/coq-community/docker-base/blob/master/Dockerfile

ENV NJOBS="8"
ENV COMPILER="4.07.1+flambda"
ENV OPAMPRECISETRACKING="1"
ENV OCAMLFIND_VERSION="1.8.1"
ENV DUNE_VERSION="2.5.1"

RUN    opam init --auto-setup --yes --jobs=${NJOBS} --compiler=${COMPILER} --disable-sandboxing         \
    && eval $(opam env)                                                                                 \
    && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
    && opam update -y                                                                                   \
    && opam install -y -j 1 opam-depext                                                                 \
    && opam pin add -n -k version ocamlfind ${OCAMLFIND_VERSION}                                        \
    && opam pin add -n -k version dune ${DUNE_VERSION}                                                  \
    && opam pin add -n -k version num 1.3                                                               \
    && opam install -y -v -j ${NJOBS} ocamlfind dune num                                                \
    && opam clean -a -c -s --logs                                                                       \
    && opam config list                                                                                 \
    && opam list

# From: https://github.com/coq-community/docker-coq/blob/master/Dockerfile

ENV COQ_VERSION="8.12.2"
ENV COQ_EXTRA_OPAM="coq-bignums coq-coq2html coq-serapi coq-rvdpdgraph"

RUN    eval $(opam env --switch=${COMPILER} --set-switch)                          \
    && opam update -y -u                                                           \
    && opam pin add -n -k version coq ${COQ_VERSION}                               \
    && opam pin add -y -n -k git https://github.com/palmskog/rvdpdgraph.git#master \
    && opam install -y -v -j ${NJOBS} coq ${COQ_EXTRA_OPAM}                        \
    && opam clean -a -c -s --logs                                                  \
    && opam config list                                                            \
    && opam list

# Setup SSH/Git/GitHub

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh

# Setup Alectryon

ENV ALECTRYON_SHA="010ebf9afd3c0c45259977895a41cba52a13b84f"

RUN    python3 -m pip install --user --upgrade pygments dominate beautifulsoup4 docutils \
    && git clone https://github.com/cpitclaudel/alectryon.git ~/alectryon                \
    && cd ~/alectryon                                                                    \
    && git checkout ${ALECTRYON_SHA}
