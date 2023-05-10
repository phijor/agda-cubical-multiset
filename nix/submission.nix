{
  src,
  stdenvNoCC,
  zip,
}: let
  zip-archive = "Multiset.zip";
in
  stdenvNoCC.mkDerivation {
    name = "Multiset-submission-archive";
    version = "0.1.0";

    inherit src;

    nativeBuildInputs = [zip];

    buildPhase = ''
      mkdir -p $out/

      cd tex/
      echo "Zipping archive ${zip-archive} ..."
      zip -r $out/${zip-archive} .
    '';
  }
