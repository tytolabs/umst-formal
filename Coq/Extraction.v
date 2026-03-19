(* ================================================================== *)
(*  UMST-Formal: Extraction.v                                          *)
(*                                                                      *)
(*  Verified extraction of gate logic to OCaml.                         *)
(*                                                                      *)
(*  This file imports Gate.v and uses Coq's extraction mechanism to     *)
(*  produce a standalone OCaml module (gate_extracted.ml) containing    *)
(*  the [gate_check] function and [ThermodynamicState] type.            *)
(*                                                                      *)
(*  WHY EXTRACT?                                                        *)
(*  The extracted OCaml serves as an independent reference              *)
(*  implementation for comparison with the Rust kernel                  *)
(*  (umst-prototype-2a).  Because it is generated from a Coq proof,    *)
(*  it is correct by construction — any discrepancy between the         *)
(*  extracted OCaml and the Rust kernel indicates a bug in Rust,        *)
(*  not in the reference.                                               *)
(*                                                                      *)
(*  EXTRACTION GUARANTEES:                                              *)
(*  Coq's extraction (Letouzey 2002) preserves computational content:  *)
(*    • Propositions (Prop) are erased — no runtime cost for proofs    *)
(*    • Types in Set/Type are mapped to OCaml types                    *)
(*    • Functions are mapped to OCaml functions                        *)
(*    • Correctness: if [gate_check s1 s2 = true] is proved in Coq,   *)
(*      the extracted OCaml function returns [true] on the same inputs *)
(*                                                                      *)
(*  WORKFLOW:                                                           *)
(*    1. coqc Gate.v               — compile proofs                    *)
(*    2. coqc Extraction.v         — generate gate_extracted.ml/.mli   *)
(*    3. ocamlfind ocamlopt ...    — compile the OCaml                 *)
(*    4. Compare output with Rust kernel on identical inputs            *)
(* ================================================================== *)

Require Import UMSTFormal.Gate.

(** Extraction configuration.

    [ExtrOcamlBasic] maps Coq's basic types to efficient OCaml types:
      • [bool]  →  OCaml [bool]  (not the inductive encoding)
      • [nat]   →  OCaml [int]   (for small naturals)
      • [list]  →  OCaml [list]

    [ExtrOcamlString] maps Coq strings to OCaml native strings.

    These mappings ensure the extracted code is idiomatic OCaml
    rather than a naive transliteration of inductive types. *)

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(** We also configure extraction of Q (rationals).
    By default, Q extracts to a pair (Z, positive) with arithmetic
    defined inductively.  This is correct but not performant.
    For a production system, one would map Q to OCaml's Zarith
    library.  For our purposes — reference testing against Rust —
    correctness matters more than speed. *)

(* ------------------------------------------------------------------ *)
(*  Extraction Commands                                                 *)
(* ------------------------------------------------------------------ *)

(** Extract [gate_check] and all its dependencies to a single file.
    This produces:
      gate_extracted.ml   — OCaml implementation
      gate_extracted.mli  — OCaml interface

    The extraction recursively pulls in:
      • [ThermodynamicState] record  →  OCaml record type
      • [gate_check]                 →  OCaml function bool
      • [Qle_bool], [Qminus], etc.  →  rational arithmetic helpers
      • [delta_mass], [Q_hyd]        →  rational constants

    Proofs ([admissible], [gate_check_correct], etc.) are erased
    because they live in Prop — zero runtime overhead. *)

Extraction "gate_extracted" gate_check.

(* ------------------------------------------------------------------ *)
(*  Post-Extraction: Compiling the OCaml                                *)
(* ------------------------------------------------------------------ *)

(*  After running [coqc Extraction.v], compile the extracted code:

      # Option A: bytecode (quick, for testing)
      ocamlfind ocamlc -package zarith -linkpkg gate_extracted.ml \
        -o gate_test

      # Option B: native (optimised, for benchmarking)
      ocamlfind ocamlopt -package zarith -linkpkg gate_extracted.ml \
        -o gate_test

    Note: the extracted code uses Coq's own integer representations
    (binary positive, Z as [Z0 | Zpos p | Zneg p]).  If you want to
    use zarith's efficient integers, define extraction mappings:

      Extract Inductive positive => "int" ["..."] "...".
      Extract Inductive Z => "int" ["0" "..." "..."] "...".

    For the reference-testing use case, the default extraction is
    sufficient — we care about logical correctness, not speed.        *)

(* ------------------------------------------------------------------ *)
(*  Comparing Extracted OCaml with Rust Kernel                          *)
(* ------------------------------------------------------------------ *)

(*  The validation workflow:

    1. Generate test vectors (random ThermodynamicState pairs)
       — use QuickCheck in Haskell, or a Python script, or Rust's
         proptest crate

    2. Run each test vector through:
       (a) The extracted OCaml [gate_check] function
       (b) The Rust kernel's [ThermodynamicFilter::check_transition]

    3. Assert identical accept/reject decisions on every vector.

    Any discrepancy is a BUG IN THE RUST KERNEL (or in the test
    harness), because the OCaml code is extracted from a verified
    Coq proof and is correct by construction.

    The Haskell layer (UMST.hs + FFI.hs) already implements this
    comparison via QuickCheck property tests.  The extracted OCaml
    provides a THIRD independent implementation for added confidence.

    This three-way comparison (Coq/OCaml, Haskell, Rust) is the
    gold standard for safety-critical verified software.              *)

(* ================================================================== *)
(*  END OF FILE                                                         *)
(* ================================================================== *)
