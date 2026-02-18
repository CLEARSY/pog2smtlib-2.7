FROM ocaml/opam AS base

FROM base AS build
RUN sudo apt update
RUN sudo apt install --yes pkg-config
RUN sudo apt install --yes libgmp-dev

RUN sudo mkdir /work
RUN sudo chown opam:opam /work
WORKDIR /work
RUN git clone --single-branch --branch master https://github.com/Gbury/dolmen.git
WORKDIR /work/dolmen
RUN opam init -a
RUN opam update
RUN opam install . --deps-only --with-test --with-doc
RUN opam exec -- make

FROM base AS final
COPY --from=build /work/dolmen/_build/default/src/bin/main.exe /usr/local/bin/dolmen
