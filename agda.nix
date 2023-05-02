{ pkgs ? import <nixpkgs> { } }:

let
  agdaDepsNames = [ "standard-library" "agda-categories" "cubical" ];
  agdaDeps = builtins.map (n:
    if n == "cubical" then
      pkgs.agdaPackages.${n}.overrideAttrs (old: {
        version = "0.4";
        src = pkgs.fetchFromGitHub {
          repo = "cubical";
          owner = "agda";
          rev = "v0.4";
          sha256 = "0ca7s8vp8q4a04z5f9v1nx7k43kqxypvdynxcpspjrjpwvkg6wbf";
        };
      })
    else
      pkgs.agdaPackages.${n}) agdaDepsNames;
  getCabalStuff = name: path:
    (builtins.filter (d: !(isNull d))
      (pkgs.haskellPackages.callCabal2nix name path { }).propagatedBuildInputs);
  haskellDeps = (getCabalStuff "HsPlot" ./Dynamical/Plot/HsPlot.cabal);
  customGhc = pkgs.haskellPackages.ghcWithPackages (ps: haskellDeps);
  nativeBuildInputs = with pkgs; [
    customGhc
    (agda.withPackages (p: agdaDeps))
  ];
  commonConfigurePhase = ''
    export AGDA_DIR=$PWD/.agda
    mkdir -p $AGDA_DIR

    for dep in ${pkgs.lib.concatStringsSep " " agdaDepsNames}; do
      echo $dep >> $AGDA_DIR/defaults
    done
  '';
  buildCommand = haskellSourcePaths: ''
    agda -c \
      ${
        pkgs.lib.concatMapStrings (path: "--ghc-flag=-i${path} ")
        haskellSourcePaths
      } \
      ${
        pkgs.lib.concatMapStrings (dep: "--ghc-flag=-package=${dep.name} ")
        haskellDeps
      } \
      --ghc-flag=-package-db=${customGhc}/lib/ghc-${customGhc.version}/package.conf.d \
      Dynamical/Plot/Plot.agda
  '';
in { inherit commonConfigurePhase nativeBuildInputs buildCommand; }
