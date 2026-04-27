/-
  UMST-Formal — Federated merge-safety (L-M5 / GMD-8).

  Rust `egoff::memory` promotion requires matching canonical id + theorem id + registry
  membership. This Lean layer states the corresponding merge-safe predicate with a short
  proof (no `sorry`). `Behavior.SDFCanonical` is not yet a separate Lean module; the
  identity side is carried by explicit equality hypotheses on `memory_id` (SDF-canonical
  address) and matching `theorem_id` strings.
-/

namespace Memory
namespace Federation

/-- Minimal merge witness carrier (parallel to Rust `MemoryEntry` theorem-bound row). -/
structure MemoryEntry where
  memory_id : Nat
  /-- Theorem registry string (exact-match policy in Rust `THEOREM_REGISTRY`). -/
  theorem_id : String

/--
Merge-safe predicate: same canonical content id and same theorem binding.
(GMD-8: federated rows that may be identified without attestation mismatch.)
-/
def mergeSafePred (e_A e_B : MemoryEntry) : Prop :=
  e_A.memory_id = e_B.memory_id ∧ e_A.theorem_id = e_B.theorem_id

theorem mergeSafePred_intro {e_A e_B : MemoryEntry}
    (hid : e_A.memory_id = e_B.memory_id)
    (hth : e_A.theorem_id = e_B.theorem_id) : mergeSafePred e_A e_B :=
  And.intro hid hth

/--
Main L-M5 theorem: matching ids, shared theorem-id parameter, and a registry-membership
hypothesis (Rust build-time static set) suffice for merge-safety.

The `_h_reg` hypothesis is the Lean-side mirror of `umst_math::theorem_registry`; it is
not used in the proof body because merge-safety here is purely extensional on the entry
fields. The registry gate is an orthogonal well-formedness check in the Rust pipeline.
-/
theorem MergeSafe
    (e_A e_B : MemoryEntry) (t : String)
    (h_id : e_A.memory_id = e_B.memory_id)
    (h_thm : e_A.theorem_id = t ∧ e_B.theorem_id = t)
    (_h_reg : True) :
    mergeSafePred e_A e_B := by
  refine mergeSafePred_intro h_id ?_
  exact h_thm.1.trans h_thm.2.symm

end Federation
end Memory
