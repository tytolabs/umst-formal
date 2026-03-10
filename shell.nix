# shell.nix — Reproducible development environment for umst-formal
#
# Enter the dev shell with:
#   nix-shell
#
# This uses the system's nixpkgs channel (<nixpkgs>), so tool versions
# track your channel.  For a fully pinned environment, replace the import
# line with a fetchTarball of a specific nixpkgs commit:
#
#   pkgs ? import (fetchTarball {
#     url    = "https://github.com/NixOS/nixpkgs/archive/<rev>.tar.gz";
#     sha256 = "<sha256>";  # run: nix-prefetch-url --unpack <url>
#   }) {}
#
# Recommended channel for exact reproducibility: nixos-24.11
# To update: nix-channel --update && nix-shell

{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "umst-formal";

  buildInputs = [
    # ── Rust ─────────────────────────────────────────────────────────
    pkgs.rustup          # Manages toolchain; edition 2021 specified in Cargo.toml

    # ── Agda ─────────────────────────────────────────────────────────
    pkgs.agda
    pkgs.agdaPackages.standard-library   # stdlib ≥ 2.1

    # ── Coq ──────────────────────────────────────────────────────────
    pkgs.coq_8_20        # Coq 8.20 (QArith, Lia, Extraction plugin)

    # ── Haskell ──────────────────────────────────────────────────────
    pkgs.ghc             # GHC ≥ 9.6 (required for CApiFFI)
    pkgs.cabal-install   # cabal ≥ 3.10

    # ── Lean 4 ────────────────────────────────────────────────────────
    pkgs.elan             # Lean version manager (reads Lean/lean-toolchain)

    # ── OCaml (for Coq extraction output) ────────────────────────────
    pkgs.ocaml
    pkgs.ocamlPackages.ocamlfind

    # ── LaTeX (for Docs/OnePager-Categorical.tex) ─────────────────────
    pkgs.texlive.combined.scheme-full

    # ── Utilities ────────────────────────────────────────────────────
    pkgs.gnumake
    pkgs.git
    pkgs.pkg-config
    pkgs.nodePackages.markdownlint-cli   # for docs CI job
  ];

  shellHook = ''
    echo ""
    echo "umst-formal dev shell"
    echo "  Agda   : $(agda --version 2>/dev/null | head -1 || echo 'not found')"
    echo "  Coq    : $(coqc --version 2>/dev/null | head -1 || echo 'not found')"
    echo "  GHC    : $(ghc --version 2>/dev/null || echo 'not found')"
    echo "  Cargo  : $(cargo --version 2>/dev/null || echo 'not found')"
    echo "  Lean   : $(lean --version 2>/dev/null | head -1 || echo 'not found (run: cd Lean && lake build)')"
    echo ""
    echo "Targets:  make agda | coq | haskell | rust | lean | full | status"
    echo ""
  '';
}
