import Lean
import rh.RS.PinchCertificate
open Lean Meta in
#eval do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.contains "buildPinch" then
      IO.println name.toString
