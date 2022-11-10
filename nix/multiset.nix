{ pkgs, path }:

let
  inherit (pkgs) agdaPackages;

  cubical = agdaPackages.cubical.overrideAttrs (oldAttrs: {
    version = "0.4prece3120d";
    src = pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "cubical";
      rev = "ce3120d3f8d692847b2744162bcd7a01f0b687eb";
      sha256 = "sha256-VkbL/wfT45lrX1vSnZn3qtSlr+aBSW4IKrRWNOTWfl8=";
    };
  });
in
agdaPackages.mkDerivation {
  pname = "Multiset";
  version = "0.1.0";
  src = builtins.path { path = path; name = "agda-cubical-multiset"; };
  everythingFile = "./Multiset/Index.lagda.md";
  buildInputs = [ cubical ];

  outputs = [ "out" "html" ];

  buildPhase = ''
    runHook preBuild

    # Make sure the README builds with --safe
    agda --html --html-dir=$html --safe README.agda

    # Build all modules that are not --safe compatible
    agda --html --html-dir=$html ./Multiset/Coinductive.agda

    runHook postBuild
  '';

  preConfigure = ''export AGDA_EXEC=agda'';
  LC_ALL = "en_US.UTF-8";
  nativeBuildInputs = [ pkgs.glibcLocales ];

  meta = {
    description = "Formalization of multisets in cubical Agda";
    homepage = "https://gitlab.cs.ttu.ee/phjora/agda-cubical-multiset";
    platforms = pkgs.lib.platforms.unix;
  };
}
