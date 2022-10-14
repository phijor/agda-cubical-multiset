{
  inputs = {
    flake-compat = {
      url = github:edolstra/flake-compat;
      flake = false;
    };
    flake-utils.url = github:numtide/flake-utils;
    nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
    nix-filter.url = github:numtide/nix-filter;
  };

  outputs = { self, nixpkgs, flake-compat, flake-utils, nix-filter, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        inherit (pkgs) agdaPackages;

        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive) scheme-medium latex-bin latexmk
            llncs
            kvoptions amsfonts stmaryrd
            newunicodechar
            mathtools amsmath
            doi csquotes cleveref
            todonotes bussproofs;
        };

        cubical = agdaPackages.cubical.overrideAttrs (oldAttrs: {
          version = "0.4prece3120d";
          src = pkgs.fetchFromGitHub {
            owner = "agda";
            repo = "cubical";
            rev = "ce3120d3f8d692847b2744162bcd7a01f0b687eb";
            sha256 = "sha256-VkbL/wfT45lrX1vSnZn3qtSlr+aBSW4IKrRWNOTWfl8=";
          };
        });

        multiset = agdaPackages.mkDerivation {
          pname = "Multiset";
          version = "0.1.0";
          src = builtins.path { path = ./.; name = "agda-cubical-multiset"; };
          everythingFile = "./Multiset/Index.lagda.md";
          buildInputs = [ cubical ];

          buildPhase = ''
            runHook preBuild

            # Make sure the README builds with --safe
            agda --safe README.agda

            # Build all modules using extra flags
            # FIXME: Figure out why this fails with 'Cannot set OPTIONS pragma --sized-types with safe flag.'
            # agda --sized-types ./Multiset/Coinductive.agda

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
        };

        paper = pkgs.stdenvNoCC.mkDerivation rec {
          name = "Multiset-in-HoTT-paper";
          src = builtins.path {
            path = nix-filter.lib.filter {
              root = ./.;
              include = [ "doc" "tex" ];
            };
            name = "tex-cubical-multiset";
          };
          buildInputs = [ pkgs.coreutils tex ];
          phases = [ "unpackPhase" "buildPhase" "installPhase" ];
          buildPhase = ''
            export PATH="${pkgs.lib.makeBinPath buildInputs}";
            mkdir -p .cache/texmf-var
            cd tex
            env TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var \
              latexmk -r latexmkrc -interaction=batchmode -halt-on-error
          '';
          installPhase = ''
            mkdir -p $out
            cd _target
            cp Multiset.pdf $out/
          '';
        };
      in
      {
        packages = {
          inherit multiset paper;
          default = multiset;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ multiset ];
        };
      }
    );
}
