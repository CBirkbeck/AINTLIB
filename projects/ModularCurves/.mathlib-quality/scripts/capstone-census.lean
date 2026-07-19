import ModularCurves.Moduli.GammaHClosure
open Lean Meta
run_meta do
  let env ← getEnv
  let inProj (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some idx => match env.header.moduleNames[idx.toNat]? with
      | some m => (`ModularCurves).isPrefixOf m | none => false
    | none => true
  let receipts : List Name := [
    `ModularCurves.gammaFullNaive_rigid_and_representable,
    `ModularCurves.gammaFullDrinfeld_rigid_and_representable,
    `ModularCurves.gammaOneDrinfeld_rigid_and_representable,
    `ModularCurves.gammaBot_representable,
    `ModularCurves.gammaH_representable_of_orderOf,
    `ModularCurves.gammaOneDrinfeld_representable_prep,
    `ModularCurves.levelSpaceΓπ_etale ]
  for r in receipts do
    match env.find? r with
    | none => IO.println s!"  {r}: MISSING"
    | some _ =>
      let mut vis : NameSet := {}; let mut q : Array Name := #[r]; let mut leaves : NameSet := {}
      while q.size > 0 do
        let n := q.back!; q := q.pop
        if vis.contains n then continue
        vis := vis.insert n
        if !inProj n then continue
        match env.find? n with
        | none => pure ()
        | some ci =>
          if ci.getUsedConstantsAsSet.contains ``sorryAx then leaves := leaves.insert n
          for u in ci.getUsedConstantsAsSet do if !vis.contains u then q := q.push u
      let ls := leaves.toList
      if ls.isEmpty then IO.println s!"  ★ {r.getString!}: CLEAN"
      else IO.println s!"  {r.getString!}: {ls.map (·.getString!)}"
