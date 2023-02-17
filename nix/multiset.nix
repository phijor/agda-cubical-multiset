{ pkgs, path }:

let
  inherit (pkgs) agdaPackages;
in
agdaPackages.mkDerivation {
  pname = "Multiset";
  version = "0.1.0";
  src = builtins.path { path = path; name = "agda-cubical-multiset"; };
  everythingFile = "./Multiset/Index.lagda.md";
  buildInputs = [ agdaPackages.cubical ];

  outputs = [ "out" "html" ];

  buildPhase = ''
    runHook preBuild

    # Make sure the README builds with --safe
    agda --html --html-dir=$html --safe README.agda

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
