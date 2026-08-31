-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- Urge overlay: packet arrival is not overlay admit. Zero new physics axioms.

module UrgeOverlay where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record OverlayCarrier : Set where
  field
    packetArrived : Bool
    suiteBound : Bool
    gateAdmit : Bool
    occupancyCanonical : Bool

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

overlayAdmissible : OverlayCarrier → Bool
overlayAdmissible c =
  (OverlayCarrier.suiteBound c ∧ OverlayCarrier.gateAdmit c) ∧ OverlayCarrier.occupancyCanonical c

tunnelOnly : OverlayCarrier
tunnelOnly = record
  { packetArrived = true
  ; suiteBound = false
  ; gateAdmit = false
  ; occupancyCanonical = false
  }

tunnelOnlyInadmissible : overlayAdmissible tunnelOnly ≡ false
tunnelOnlyInadmissible = refl

data OverlayAdminPlane : Set where
  lanPlane : OverlayAdminPlane
  wireGuardPlane : OverlayAdminPlane
  tailscaleFallback : OverlayAdminPlane

productionAdminPlaneAdmissible : OverlayAdminPlane → Bool
productionAdminPlaneAdmissible tailscaleFallback = false
productionAdminPlaneAdmissible _ = true

tailscaleNotProduction : productionAdminPlaneAdmissible tailscaleFallback ≡ false
tailscaleNotProduction = refl

lanWgEligible :
  productionAdminPlaneAdmissible lanPlane ≡ true
lanWgEligible = refl
