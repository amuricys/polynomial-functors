{ pkgs ? import <nixpkgs> {} }:

let
  agdaDepsNames = [
    "standard-library"
    "agda-categories"
    "cubical"
  ];
  agdaDeps = builtins.map (n: if n == "cubical" then pkgs.agdaPackages.${n}.overrideAttrs (old: {
        version = "0.4";
        src = pkgs.fetchFromGitHub {
          repo = "cubical";
          owner = "agda";
          rev = "v0.4";
          sha256 = "0ca7s8vp8q4a04z5f9v1nx7k43kqxypvdynxcpspjrjpwvkg6wbf";
        };
      }) else pkgs.agdaPackages.${n}) agdaDepsNames;

  buildAgdaBinary = agdaSrc: binName: haskellDeps: haskellSrcPath: let
    customGhc = pkgs.haskellPackages.ghcWithPackages (ps: haskellDeps);
  in
  pkgs.stdenv.mkDerivation {
    name = binName;
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
      echo "agda -c \
        --ghc-flag=-i${haskellSrcPath} \
        --ghc-flag=-iDynamical/Matrix/src \
        ${pkgs.lib.concatMapStrings (dep: "--ghc-flag=-package=${dep.name} ") haskellDeps} \
        --ghc-flag=-package-db=${customGhc}/lib/ghc-${customGhc.version}/package.conf.d \
        ${agdaSrc}"
      agda -c \
        --ghc-flag=-i${haskellSrcPath} \
        --ghc-flag=-iDynamical/Matrix/src \
        ${pkgs.lib.concatMapStrings (dep: "--ghc-flag=-package=${dep.name} ") haskellDeps} \
        --ghc-flag=-package-db=${customGhc}/lib/ghc-${customGhc.version}/package.conf.d \
        ${agdaSrc}
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp $TMP/poly/${binName} $out/bin
    '';

    meta = with pkgs.lib; {
      description = "A simple Agda project that builds a binary from Agda source";
      license = licenses.mit;
    };
  };
  getCabalStuff = name: path: (builtins.filter (d: !(isNull d)) (pkgs.haskellPackages.callCabal2nix name path {}).propagatedBuildInputs);
  plot = buildAgdaBinary "Dynamical/Plot/Plot.agda" "plot" (getCabalStuff "HsPlot" ./Dynamical/Plot/HsPlot.cabal) "Dynamical/Plot/src";
  pseudoInverse = buildAgdaBinary "Dynamical/Matrix/PseudoInverse.agda" "pseudoInverse" (getCabalStuff "HsMatrix" ./Dynamical/Matrix/HsMatrix.cabal) "Dynamical/Matrix/src";
in
{
  plot = plot;
#  pseudoInverse = pseudoInverse;
}
