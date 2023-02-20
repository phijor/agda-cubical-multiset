{
  src,
  stdenvNoCC,
  gnutar,
  gzip,
  zip,
}: let
  tarball = "Multiset.tar.gz";
  zip-archive = "Multiset.zip";
in
  stdenvNoCC.mkDerivation {
    name = "Multiset-repo-archive";
    version = "0.1.0";

    inherit src;

    nativeBuildInputs = [gzip gnutar zip];

    buildPhase = ''
      mkdir -p $out/

      echo "Creating tarball ${tarball} ..."
      tar --create --verbose --gzip --file $out/${tarball} .

      echo "Zipping archvie ${zip-archive} ..."
      zip -r $out/${zip-archive} .
    '';
  }
