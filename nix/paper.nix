{ pkgs, doc, src }:

let
  tex = pkgs.texlive.combine {
    inherit (pkgs.texlive) scheme-medium latex-bin latexmk
      llncs
      kvoptions amsfonts stmaryrd
      newunicodechar
      mathtools amsmath
      doi csquotes cleveref
      todonotes bussproofs;
  };

  buildInputs = [ pkgs.coreutils tex ];
  docDir = builtins.dirOf doc;
in
pkgs.stdenvNoCC.mkDerivation {
  inherit src buildInputs;
  name = "Multiset-in-HoTT-paper";
  phases = [ "unpackPhase" "buildPhase" "installPhase" ];
  buildPhase = ''
    export PATH="${pkgs.lib.makeBinPath buildInputs}";
    mkdir -p .cache/texmf-var
    env TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var \
      latexmk \
        -pdf \
        -cd \
        -interaction=batchmode \
        -halt-on-error \
        ${doc}
  '';
  installPhase = ''
    mkdir -p $out
    cp ${docDir}/*.pdf $out/
  '';
}
