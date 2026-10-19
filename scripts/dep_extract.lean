import ECRuntime

/-!
# Proof-dependency extractor

Walks the compiled environment and records, for every `ECRuntime` declaration, the
other `ECRuntime` declarations its **statement and proof term actually mention**.

This is the real dependency network. An import graph only says which modules were
made available; this says which results a proof genuinely rests on, so an import
that is never used shows up as an absent edge rather than a spurious one.

Run with:

    lake env lean scripts/dep_extract.lean

It writes `.verify/deps.tsv` with one `source<TAB>target` edge per line, plus
`.verify/decls.tsv` with `name<TAB>module<TAB>kind`.
-/

open Lean

namespace ECRuntimeDepExtract

/-- A declaration's defining term, including a theorem's proof.

`ConstantInfo.value?` deliberately returns `none` for theorems -- it will not hand back
a proof term. Using it here silently produced a *statement*-level graph while claiming
to be a proof-level one: every edge that existed only inside a proof was missing, and
nothing looked obviously wrong. Match the constructor instead. -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Constants referenced by a declaration's type and its defining term. -/
def usedConstants (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match valueOf info with
  | some v => fromType ++ v.getUsedConstants
  | none => fromType

/-- Keep only declarations belonging to this development, skipping the internal
names Lean generates (`_proof_1`, `.match_2`, `.eq_def`, instances, and so on). -/
def isOwn (n : Name) : Bool :=
  (`ECRuntime).isPrefixOf n && !n.isInternal && !n.hasMacroScopes

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "ctor"
  | .inductInfo _ => "inductive"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

end ECRuntimeDepExtract

open ECRuntimeDepExtract in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut edges : Array (Name × Name) := #[]
  let mut decls : Array (Name × Name × String) := #[]

  for (name, info) in env.constants.toList do
    unless isOwn name do continue
    let modName :=
      match env.getModuleFor? name with
      | some m => m
      | none => `unknown
    decls := decls.push (name, modName, kindOf info)
    let mut seen : NameSet := {}
    for c in usedConstants info do
      if isOwn c && c != name && !seen.contains c then
        seen := seen.insert c
        edges := edges.push (name, c)

  IO.FS.createDirAll ".verify"

  let edgeLines := edges.map (fun (a, b) => s!"{a}\t{b}")
  IO.FS.writeFile ".verify/deps.tsv" (String.intercalate "\n" edgeLines.toList ++ "\n")

  let declLines := decls.map (fun (n, m, k) => s!"{n}\t{m}\t{k}")
  IO.FS.writeFile ".verify/decls.tsv" (String.intercalate "\n" declLines.toList ++ "\n")

  IO.println s!"declarations: {decls.size}"
  IO.println s!"edges:        {edges.size}"
