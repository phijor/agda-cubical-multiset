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
        multiset = import ./nix/multiset.nix {
          inherit pkgs;
          path = ./.;
        };
        paper = import ./nix/paper.nix {
          inherit pkgs;
          doc = "tex/Multiset.tex";
          src = nix-filter.lib.filter {
              root = ./.;
              name = "tex-cubical-multiset";
              include = [ "doc" "tex" ];
            };
          };
        archive = pkgs.callPackage ./nix/archive.nix {
          src = nix-filter.lib.filter {
            root = ./.;
            name = "archive-cubical-multiset";
            include = [
              "README.md"
              "README.agda"
              "LICENSE"

              # The Agda library
              "Multiset/"
              "Multiset.agda-lib"

              # Building with Nix
              "nix"
              (nix-filter.lib.matchExt "nix")
              "flake.lock"
            ];
          };
        };
        submission = pkgs.callPackage ./nix/submission.nix {
          src = nix-filter.lib.filter {
            root = ./.;
            name = "submission-cubical-multiset";
            include = [
              # TeX main file
              "tex/Multiset.tex"

              # Bibliography (one is a symlink)
              "doc/Multiset.bib"
              "tex/Multiset.bib"

              # TeX style and document class
              "tex/multiset.sty"
              "tex/lipics-v2021.cls"

              # Supplementary graphics
              "tex/cc-by.pdf"
              "tex/orcid.pdf"
              "tex/lipics-logo-bw.pdf"

              # latexmk configuration
              "tex/latexmkrc"
            ];
          };
        };
      in
      {
        packages = {
          inherit multiset paper archive submission;
          default = multiset;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ multiset ];
        };
      }
    );
}
