/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

namespace CasCatalogue.Language

/-- The items of a file: its blank-line-separated paragraphs, without comment lines. -/
meta def items (text : String) : Array String := Id.run do
  let mut out := #[]
  let mut current := ""
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "--" then continue
    if t.isEmpty then
      unless current.isEmpty do out := out.push current
      current := ""
    else current := if current.isEmpty then line else current ++ "\n" ++ line
  unless current.isEmpty do out := out.push current
  return out

end CasCatalogue.Language
