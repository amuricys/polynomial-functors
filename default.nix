{ pkgs ? import <nixpkgs> {} }:

let
  # So that we don't have to repeat ourselves in the configurePhase and the
  # agdaDeps variable.
  agdaDepsNames = [
    "standard-library"
    "agda-categories"
    "cubical"
  ];
  agdaDeps = builtins.map (n: pkgs.agdaPackages.${n}) agdaDepsNames;
  
  haskellDeps = 
    builtins.filter (d: !(isNull d)) (pkgs.haskellPackages.callCabal2nix "HsPlot" ./Dynamical/Plot/HsPlot.cabal {}).propagatedBuildInputs;
  # Create a custom GHC environment with the needed dependencies. What this will do is "install"
  # a GHC that has a package db listing the dependencies in the cabal file.
  customGhc = pkgs.haskellPackages.ghcWithPackages (ps: haskellDeps);

in
pkgs.stdenv.mkDerivation {
  name = "plot";
  src = ./.;

  nativeBuildInputs = with pkgs; [
    customGhc
    (agda.withPackages (p: agdaDeps))
  ];

  configurePhase = ''
    export AGDA_DIR=$PWD/.agda
    mkdir -p $AGDA_DIR

    for dep in ${pkgs.lib.concatStringsSep " " agdaDepsNames}; do
      echo $dep >> $AGDA_DIR/defaults
    done
  '';

  buildPhase = ''
    agda -c \
      --ghc-flag=-iDynamical/Plot/src \
      ${pkgs.lib.concatMapStrings (dep: "--ghc-flag=-package=${dep.name} ") haskellDeps} \
      --ghc-flag=-package-db=${customGhc}/lib/ghc-${customGhc.version}/package.conf.d \
      Dynamical/Plot/Plot.agda
  '';

  installPhase = ''
    mkdir -p $out/bin
    cp $TMP/poly/Plot $out/bin
  '';

  meta = with pkgs.lib; {
    description = "A simple Agda project that plots data using the Chart library";
    license = licenses.mit;
  };
}