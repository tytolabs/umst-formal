(* ================================================================== *)
(*  UMST-Formal: MeasurementCost.v                                      *)
(*                                                                      *)
(*  Formal bounds on the physical energy required to perform a          *)
(*  measurement, linking information gain (mutual information) to       *)
(*  Landauer's principle.                                               *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra Field.
Require Import UMSTFormal.LandauerEinsteinBridge.

Open Scope R_scope.

(** The absolute minimum energy required to perform a measurement that gains 
    [MI_bits] bits of information at temperature [T].
    By Landauer's Principle, erasing the generated records requires energy
    equal to `kB * T * ln(2) * MI_bits`. This sets a physical lower bound. *)
Definition measurementEnergyLowerBound (T MI_bits : R) : R :=
  MI_bits * E_Landauer_bit T.

(** Trivial bound: if the measurement gains zero information, 
    the theoretic lower energy bound for the acquisition is zero. *)
Lemma zero_info_zero_energy (T : R) :
  measurementEnergyLowerBound T 0 = 0.
Proof.
  unfold measurementEnergyLowerBound.
  ring.
Qed.
