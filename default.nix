{ pkgs ? import <nixpkgs> { } }:

let
  agda = import ./agda.nix { inherit pkgs; };
  binName = "plot";
in pkgs.stdenv.mkDerivation {
  name = binName;
  src = ./.;
  nativeBuildInputs = agda.nativeBuildInputs;
  configurePhase = agda.commonConfigurePhase;
  buildPhase = agda.buildCommand [ "Dynamical/Plot/src" "Dynamical/Matrix/src" ] ;
  installPhase = ''
    mkdir -p $out/bin
    cp $TMP/poly/${binName} $out/bin
  '';
}
