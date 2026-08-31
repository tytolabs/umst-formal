-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.OverlayCompose
-- Description : Packets on L3 are not overlay admit (Tailscale/WG tunnel = trust refused).
--
-- Overlay admit = suiteBound && gateAdmit && occupancyCanonical.
-- Occupancy remainder SDF is replica-lag identity — not MagicDNS.
-- Sole physics axiom remains Lean LandauerLaw.physicalSecondLaw (cited, not restated).
module UMST.Urge.OverlayCompose
  ( OverlayCarrier (..)
  , overlayAdmissible
  , tunnelOnly
  , packetArrivalNotSufficient
  , occupancyRemainderAdmissible
  ) where

data OverlayCarrier = OverlayCarrier
  { packetArrived :: Bool
  , suiteBound :: Bool
  , gateAdmit :: Bool
  , occupancyCanonical :: Bool
  } deriving (Eq, Show)

overlayAdmissible :: OverlayCarrier -> Bool
overlayAdmissible c =
  suiteBound c && gateAdmit c && occupancyCanonical c

tunnelOnly :: OverlayCarrier
tunnelOnly = OverlayCarrier
  { packetArrived = True
  , suiteBound = False
  , gateAdmit = False
  , occupancyCanonical = False
  }

-- | Packet arrival is never sufficient when suite is unbound.
packetArrivalNotSufficient :: OverlayCarrier -> Bool
packetArrivalNotSufficient c =
  not (suiteBound c) && not (overlayAdmissible c)

occupancyRemainderAdmissible :: Double -> Double -> Bool
occupancyRemainderAdmissible remainder budget =
  remainder <= budget && budget >= 0
