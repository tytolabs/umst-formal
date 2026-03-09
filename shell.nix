# shell.nix — Reproducible development environment for umst-formal
#
# Enter the dev shell:
#   nix-shell
#
# For flakes (experimental):
#   nix develop
#
# Tool versions pinned here correspond to the versions used during the
# initial publication of this repository (March 2026).
# To update a tool, change the rev and update the sha256 via:
#   nix-prefetch-url --unpack <url>

{ pkgs ? import (fetchTarball {
    # nixpkgs 24.11 (stable, March 2026)
    url    = "https://github.com/NixOS/nixpkgs/archive/nixos-24.11.tar.gz";
    sha256 = "0000000000000000000000000000000000000000000000000000"; # update with real hash
  }) {}
}:

pkgs.mkShell {
  name = "umst-formal";

  buildInputs = [
    # ── Rust (via rustup overlay or fixed toolchain) ──────────────────
    pkgs.rustup            # manages stable/nightly; Cargo.toml pins edition=2021

    # ── Agda ─────────────────────────────────────────────────────────
    pkgs.agda              # Agda ≥ 2.6.4
    pkgs.agdaPackages.standard-library   # Agda stdlib ≥ 2.1

    # ── Coq ──────────────────────────────────────────────────────────
    pkgs.coq_8_20          # Coq 8.20.x (QArith, Lia, extraction)

    # ── Haskell ──────────────────────────────────────────────────────
    pkgs.ghc               # GHC ≥ 9.6 (required for CApiFFI)
    pkgs.cabal-install     # cabal ≥ 3.10
    pkgs.haskellPackages.QuickCheck  # pinned in cabal file too

    # ── OCaml (for Coq extraction output) ────────────────────────────
    pkgs.ocaml             # OCaml ≥ 5.1
    pkgs.ocamlPackages.ocamlfind

    # ── LaTeX (for Docs/OnePager-Categorical.tex) ─────────────────────
    pkgs.texlive.combined.scheme-full

    # ── Utilities ────────────────────────────────────────────────────
    pkgs.gnumake
    pkgs.git
    pkgs.pkg-config
  ];

  shellHook = ''
    echo ""
    echo "umst-formal dev shell"
    echo "  Agda:   $(agda --version 2>/dev/null || echo 'not found')"
    echo "  Coq:    $(coqc --version 2>/dev/null | head -1 || echo 'not found')"
    echo "  GHC:    $(ghc --version 2>/dev/null || echo 'not found')"
    echo "  Cargo:  $(cargo --version 2>/dev/null || echo 'not found')"
    echo ""
    echo "Quick-start:"
    echo "  Agda  → cd Agda  && make check"
    echo "  Coq   → cd Coq   && make"
    echo "  Haskell → cd Haskell && cabal test"
    echo "  Rust  → cd ffi-bridge && cargo test"
    echo ""
  '';
}
