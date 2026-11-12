{ pkgs, argent }:
let
  rocq = pkgs.rocqPackages_9_3;
  ocaml = rocq.rocq-core.ocamlPackages;
  common = [
    rocq.rocq-core
    rocq.stdlib
    rocq.rocq-elpi
    argent
    ocaml.ocaml
    ocaml.findlib
    ocaml.dune_3
    ocaml.ocamlformat
    pkgs.just
    pkgs.git
    pkgs.ripgrep
  ];
  shellHook = ''
    export DUNE_CACHE=enabled
    export DUNE_CACHE_STORAGE_MODE=hardlink
    export DUNE_CACHE_ROOT="''${XDG_CACHE_HOME:-$HOME/.cache}/galois/dune"
    unset LD_LIBRARY_PATH
  '';
in
{
  devShell = pkgs.mkShell {
    packages = common ++ [ rocq.flocq ocaml.core ocaml.core_unix ocaml.ppx_jane ocaml.ppx_expect ];
    inherit shellHook;
  };
  sessionShell = pkgs.mkShell {
    packages = common;
    inherit shellHook;
  };
}
