{ pkgs, path }:

let
  inherit (pkgs) agdaPackages;
in
agdaPackages.mkDerivation {
  pname = "Multiset";
  version = "0.1.0";
  src = builtins.path { path = path; name = "agda-cubical-multiset"; };
  buildInputs = [ agdaPackages.cubical ];

  outputs = [ "out" "html" ];

  postBuild = ''
    # Make sure the README builds with --safe
    agda --html --html-dir=$html --highlight-occurrences --safe README.agda
  '';

  meta = {
    description = "Formalization of multisets in cubical Agda";
    homepage = "https://gitlab.cs.ttu.ee/phjora/agda-cubical-multiset";
    platforms = pkgs.lib.platforms.unix;
  };
}
