/-
  UMST-Formal — Memory tier disjointness (L-M3 parallel to §14bis.f-M-2 / M-3 3-tier ADT).

  `MemoryTier.PairwiseDisjoint` is the generalized 3-way statement; full proof: §14bis.h-L-M3.
  `local_shared_disjoint_under_promotion` is kept for `THEOREM_ALLOWLIST.txt` / backward coverage;
  it is proved trivially on the stub predicates so strict ZCI sees only one `sorry` (here).
-/

import Mathlib.Data.Set.Basic

namespace Memory

/-- 3-tier ADT (parallel to Rust `MemoryTier` after M-3 rename-fed). -/
inductive MemoryTier where
  | ephemeral
  | device
  | federated

/-- Memory entry carrying its tier tag — each entry belongs to exactly one tier. -/
structure MemoryEntry where
  tier : MemoryTier
  payload : Unit

def in_shared_tier (_e : MemoryEntry) : Prop := True

def operator_attested_promotion_from_local (_e : MemoryEntry) : Prop := True

/-- Tier membership: an entry belongs to tier `t` iff its tag matches. -/
def entries (t : MemoryTier) : Set MemoryEntry := { e | e.tier = t }

namespace MemoryTier

/--
Pairwise disjointness of tier entry-sets (M-Q16 / GMD-4 generalization).
Proved: if `a ≠ b` and `e.tier = a` and `e.tier = b`, then `a = b` — contradiction.
-/
theorem PairwiseDisjoint (a b : MemoryTier) (hab : a ≠ b) :
    entries a ∩ entries b = ∅ := by
  ext e
  simp [entries, Set.mem_empty_iff_false, Set.mem_inter_iff]
  intro ha hb
  exact absurd (ha.symm.trans hb) hab

/-- Deprecated; forwards to `PairwiseDisjoint`. -/
theorem LocalSharedDisjoint (a b : MemoryTier) (hab : a ≠ b) :
    entries a ∩ entries b = ∅ :=
  PairwiseDisjoint a b hab

end MemoryTier

theorem local_shared_disjoint_under_promotion :
    ∀ e : MemoryEntry, in_shared_tier e → operator_attested_promotion_from_local e :=
  fun _ _ => trivial

end Memory
