{ pkgs ? import <nixpkgs> {} }:

let
  agda = import ./agda.nix { inherit pkgs; };
in pkgs.mkShell {
  nativeBuildInputs = agda.nativeBuildInputs;
  configurePhase = agda.commonConfigurePhase;
  shellHook = ''
    export build="${agda.buildCommand [ "Dynamical/Plot/src" "Dynamical/Matrix/src" ]}"
  '';
}
