# Formal physics derivation plan — mathematical scope and proof obligations

This document specifies **what it would mean** to *derive* (not merely cite) several
physics statements inside an extended formal theory, and **why** they are **not**
theorems of the current `umst-formal` core.  It avoids empirical speculation: it
classifies claims by **logical and model-theoretic prerequisites** only.

**Companion:** `Docs/FORMAL-PHYSICS-ROADMAP.md` (phased engineering plan).  
**Status index:** `PROOF-STATUS.md`.

---

## 0. How “cannot be proven” is stated mathematically

Let **L₀** be the formal language of the current mechanized core: discrete (or
rational-scoped) thermodynamic states, the `admissible` transition predicate,
Helmholtz/SDF fragments, Kleisli composition, and the Landauer–Einstein **algebraic**
bridge (definitions + SR identity applied to a **chosen** energy scale \(k_B T\ln 2\)).

### 0.1 Not even a well-formed proposition in L₀ (strongest, accurate statement)

Many targets below quantify over objects **absent from L₀**, for example:

- smooth Lorentzian manifolds \((M,g)\),
- quantum channels / explicit erasure processes on a device state space,
- black-hole horizons with area functionals,
- homogeneous cosmological scale factors \(a(t)\).

In first-order / dependent-type practice: if the **symbols and types do not exist**
in the theory, the sentence is **not expressible**.  Then:

> It is not a matter of “missing a clever proof”: the claim is **outside the
> signature** until definitions import those types.

This is the mathematically accurate sense in which the current artifact **does not
prove** Jacobson, Bekenstein, Friedmann, or Landauer-as-law.

### 0.2 Relative derivation: theorem *in an extended theory* T_ext

To **derive** a physical statement **S** means:

1. **Define** a theory **T_ext = L₀ + ΔL** (new sorts, constants, axioms **A_ext**).
2. Either prove **T_ext ⊢ S** or exhibit **S** as an explicit **axiom** in **A_ext**
   (honest if the physics is taken as primitive in that layer).
3. Record every item of **A_ext** in `PROOF-STATUS.md` (no hidden postulates).

**Scientific alignment:** Nature is not decided by proof assistants; **T_ext** is a
*mathematical model*.  Validity of **A_ext** relative to experiment is **external**
to the formal proof.

### 0.3 What this document does *not* claim

- It does **not** assert that any **A_ext** is “true in reality.”
- It does **not** replace textbooks or peer-reviewed derivations; it lists **proof
  obligations** and **dependencies** so mechanization can be staged without ambiguity.

---

## 1. Landauer bound as a *derived* law (not the algebraic scale alone)

### 1.1 Already mechanized (definition + SR)

Combining the **definition** “Landauer energy per bit at temperature \(T\) is
\(k_B T\ln 2\)” with **\(E=mc^2\)** yields the mass equivalent — this is **pure
algebra + real analysis** (Lean) or parameters (Coq).  No claim is made that any
**physical process** must pay that energy.

### 1.2 Target sentence S_Landauer (thermodynamic law form)

A typical formal shape (schematic):

> For every **erasure process** \(\mathcal{E}\) in a class **𝒞** of thermodynamically
> closed operations that **logically erase** one bit of information about a
> specified subsystem, the **average work** supplied satisfies
> \(\langle W\rangle \ge k_B T\ln 2\) (isothermal, temperature \(T\), suitable
> entropy accounting).

**ΔL required:**

| Ingredient | Role |
|------------|------|
| Type of **microstates** / device + reservoir | state space \(\Omega\) |
| **Entropy** functional \(S\) (Gibbs, von Neumann, or operational) | second-law bookkeeping |
| Class **𝒞** of **processes** (CPTP maps, stochastic kernels, …) | what “erasure” means |
| **Logical irreversibility** predicate on maps | distinguishes reset-to-zero from reversible maps |
| **Second law** as axiom or as **theorem** from microscopic dynamics | supplies \(\Delta S \ge 0\) style input |

**Proof pattern (standard in statistical mechanics / quantum thermodynamics):**
relate work to free-energy change; lower bound from **data-processing** or
**entropy increase** under the chosen class **𝒞**.  The bound is **conditional** on
the entropy definition and the process class.

**Milestone for `umst-formal`:**

1. Module `LandauerLaw.lean` (or Coq): definitions of \(\mathcal{E}\), **𝒞**, \(S\).
2. Axiom bundle **A_Landauer_base** (e.g. second law on \(S\) for **𝒞**) **or**
   microscopic Hamiltonian + theorem proving second law.
3. Theorem `landauer_bound : ∀ ε ∈ 𝒞, …` with hypotheses explicit in the statement.

Until then, **S_Landauer** is **not a wff** in L₀ and is **not proved** here.

---

## 2. “Information mass” beyond the SR bridge (gravitational coupling)

### 2.1 Already mechanized

**m_eq** from \(k_B T\ln 2\) and \(E=mc^2\) is a **number** attached to a **defined**
energy scale.  No gravitational field equations are used.

### 2.2 Target sentences S_grav (examples of distinct strengthenings)

These are **different** and must not be conflated:

| Variant | Schematic content | Prerequisites beyond L₀ |
|---------|-------------------|-------------------------|
| **S_SR** | Passive mass–energy equivalence for the **same** energy | Already in Landauer–Einstein fragment (SR only). |
| **S_Einstein** | Stress–energy tensor \(T_{\mu\nu}\) contributes to **\(G_{\mu\nu}=8\pi G T_{\mu\nu}\)** | Lorentzian geometry, Einstein equations, specification of \(T_{\mu\nu}\) for “information” degrees of freedom |
| **S_meas** | Operational **measurement protocol** ties \(m_{\mathrm{eq}}\) to a **weighing** experiment | Experimental design as mathematical model (forces, coupling, calibration) |

**ΔL for S_Einstein:** differentiable manifold, metric, matter fields, **G**, **ħ**
if quantum matter; choice of how “information” enters **\(T_{\mu\nu}\)** (e.g. as
expectation of a field operator, or as phenomenological fluid — each choice is a
**different** extension).

**Mathematically accurate status:** **S_Einstein** and **S_meas** are **not** in L₀.
They require **T_GR** (or an effective theory) plus an explicit **interpretation map**
from formal “information” to **\(T_{\mu\nu}\)**.  That map is **not determined** by
logic alone — it is **model choice**, to be listed as definition or axiom.

---

## 3. Jacobson-style “Einstein equations from thermodynamics”

### 3.1 Target shape (schematic)

From **local Rindler horizons**, **heat** \(\delta Q\), **Unruh temperature**, and a
**first-law** / Clausius-type postulate, derive **field equations** for \(g_{\mu\nu}\)
(or an equivalent geometric dynamics).

### 3.2 Prerequisites ΔL

| Object | Purpose |
|--------|---------|
| Lorentzian **\((M,g)\)** | spacetime |
| **Local boost generators** / horizon generators | identify local acceleration temperature |
| **Energy–momentum flux** through horizon | define \(\delta Q\) |
| **Entropy functional** for horizon (often **Bekenstein–Hawking** \(S=A/4G\hbar\)) | links area change to heat |
| **Clausius-type relation** | \(\delta Q = T\,\delta S\) along specified virtual displacements |
| **Equivalence principle** / locality assumptions | justify Rindler patch arguments |

**Status:** This is a **theorem in a named geometric–thermodynamic axiom system**, not
in L₀.  Mechanization = build **T_Jacobson** with the above sorts; prove implication
to Einstein tensor equations under stated hypotheses (matching one published variant).

---

## 4. Bekenstein / holographic entropy bounds

### 4.1 Target shape (schematic)

> For spacetimes and matter in class **ℋ**, entropy \(S\) of region **R** satisfies
> \(S \le A/(4G\hbar)\) (or a chosen variant with explicit energy conditions).

### 4.2 Prerequisites ΔL

- Definition of **entropy** for the physical content (QFT on curved spacetime,
  black-hole entropy, etc.).
- **Energy conditions** (NEC, ANEC, …) as hypotheses.
- Often **semiclassical** or **quantum gravity** input.

**Status:** **Not in L₀**.  Each literature theorem is **relative** to its **ℋ** and
entropy definition.  Formal work = fix **one** variant, encode **ℋ** and axioms,
then prove or adopt as axiom.

---

## 5. Friedmann equations and information density \(\rho_i\)

### 5.1 Target shape (schematic)

**Cosmological symmetry** (homogeneity + isotropy) + **Einstein equations** + stress–energy
tensor \(T_{\mu\nu}\) (including a term labelled “information” or not) \(\Rightarrow\)
ODEs for scale factor \(a(t)\) (Friedmann equations).

### 5.2 Prerequisites ΔL

| Ingredient | Role |
|------------|------|
| FLRW **metric ansatz** | reduces PDEs to ODEs |
| **\(T_{\mu\nu}\)** for matter + any \(\rho_i\) term | closure of the system |
| **Equation of state** \(w\) for each component | needed for closed ODE |

**Status:** The **ODE** is a **theorem** once the ansatz and **\(T_{\mu\nu}\)** are
**defined**.  Whether a separate **\(\rho_i\)** is **physically motivated** is **not**
a logical consequence of the gate formalism — it is an **additional constitutive**
specification in **T_cosmo**.

---

## 6. Dependency graph (high level)

```text
L₀ (gate + Landauer–Einstein algebra)
  │
  ├─► T_LandauerLaw     = L₀ + processes + entropy + second law / microdynamics
  ├─► T_GR              = L₀ + Lorentzian geometry + Einstein equations + …
  │       ├─► T_Jacobson   (horizon thermodynamics + Clausius on horizons)
  │       ├─► T_Bekenstein (entropy definition + energy conditions + …)
  │       └─► T_Friedmann  (FLRW + T_μν + EOS)
  └─► T_interpretation   = explicit maps from “information” symbols to T_μν / devices
```

No edge implies **“true in Nature”**; edges are **proof dependencies** only.

---

## 7. Action items for mechanization (non-speculative checklist)

| Step | Action |
|------|--------|
| 1 | For each target **S**, write the **exact** dependent-type statement (no hidden quantifiers). |
| 2 | List **ΔL** and **A_ext**; add rows to `PROOF-STATUS.md`. |
| 3 | Prove **S** in **T_ext** **or** leave **S** as named **axiom** in **T_ext** (declared). |
| 4 | If **S** is left as axiom, **do not** describe it as “derived from the gate.” |
| 5 | Prefer **minimal** extensions: multiple small theories **T₁**, **T₂** rather than one ambiguous mega-theory. |

---

## 8. Summary table

| Topic | In L₀ today? | To derive as a theorem | Typical alternative (honest) |
|-------|----------------|-------------------------|------------------------------|
| Landauer **scale** + SR mass | Yes (definitions + analysis) | N/A (already algebraic) | — |
| Landauer **law** for processes | **No** | Extend with **𝒞**, \(S\), second law / microdynamics | Axiom bundle for **𝒞** + \(S\) |
| Gravitational coupling of “information” | **No** | **T_GR** + explicit **\(T_{\mu\nu}\)** map | Phenomenological axiom for **\(T_{\mu\nu}\)** |
| Jacobson | **No** | **T_Jacobson** with horizon thermodynamics | Axiom: first law + entropy of horizon |
| Bekenstein bound | **No** | **T_Bekenstein** with fixed **ℋ**, \(S\) | Axiom: bound as primitive |
| Friedmann + \(\rho_i\) | **No** | **T_Friedmann** with FLRW + **\(T_{\mu\nu}\)** | Axiom: \(\rho_i\) as fluid component |

This is the mathematically accurate account: **either** extend the language and
prove **S** relative to explicit **A_ext**, **or** admit **S** as an axiom in that
extension, **or** keep **S** unformalized — without claiming it follows from **L₀**.
