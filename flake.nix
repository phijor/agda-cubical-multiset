{
  inputs = {
    flake-compat = {
      url = github:edolstra/flake-compat;
      flake = false;
    };
    flake-utils.url = github:numtide/flake-utils;
    nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  };

  outputs = { self, nixpkgs, flake-compat, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
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

        multiset = agdaPackages.mkDerivation {
          pname = "Multiset";
          version = "0.1.0";
          src = builtins.path { path = ./.; name = "agda-cubical-multiset"; };
          everythingFile = "./Multiset/Index.lagda.md";
          buildInputs = [ cubical ];

          preConfigure = ''export AGDA_EXEC=agda'';
          LC_ALL = "en_US.UTF-8";
          nativeBuildInputs = [ pkgs.glibcLocales ];

          meta = {
            description = "Formalization of multisets in cubical Agda";
            homepage = "https://gitlab.cs.ttu.ee/phjora/agda-cubical-multiset";
            platforms = pkgs.lib.platforms.unix;
          };
        };
      in
      {
        packages = {
          inherit multiset;
          default = multiset;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ multiset ];
          packages = [ ];
        };

        defaultPackage = self.packages.default;
        devShell = self.devShells.default;
      }
    );
}
