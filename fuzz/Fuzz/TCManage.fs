module Smartian.TCManage

open System.Collections.Generic
open Nethermind.Evm
open Executor
open Options
open Utils
open Nethermind.Dirichlet.Numerics
open Nethermind.Core.Test.Builders
open Nethermind.Core.Specs
open Nethermind.Evm.Test
open Nethermind.Evm.Tracing
open Nethermind.Logging
open Nethermind.Store

(*** Directory paths ***)

let mutable tcDir = ""
let mutable bugDir = ""

let initialize outDir =
  tcDir <- System.IO.Path.Combine(outDir, "testcase")
  System.IO.Directory.CreateDirectory(tcDir) |> ignore
  bugDir <- System.IO.Path.Combine(outDir, "bug")
  System.IO.Directory.CreateDirectory(bugDir) |> ignore

(*** Statistics ***)

let mutable private totalTC = 0
let mutable private totalBug = 0
let mutable private totalAF = 0
let mutable private totalAW = 0
let mutable private totalBD = 0
let mutable private totalCH = 0
let mutable private totalEL = 0
let mutable private totalIB = 0
let mutable private totalME = 0
let mutable private totalMS = 0
let mutable private totalRE = 0
let mutable private totalSC = 0
let mutable private totalTO = 0
let mutable private totalFE = 0
let mutable private totalRV = 0

let checkFreezingEtherBug () =
  if receivedEther && useDelegateCall && not canSendEther then
    totalFE <- totalFE + 1

let printStatistics () =
  log "Total Executions: %d" totalExecutions
  log "Deployment failures: %d" deployFailCount
  log "Test Cases: %d" totalTC
  log "Covered Edges: %d" accumEdges.Count
  log "Covered Instructions: %d" accumInstrs.Count
  log "Covered Def-Use Chains: %d" accumDUChains.Count
  log "Found Bugs:"
  log "  Assertion Failure: %d" totalAF
  log "  Arbitrary Write: %d" totalAW
  log "  Block state Dependency: %d" totalBD
  log "  Control Hijack: %d" totalCH
  log "  Ether Leak: %d" totalEL
  log "  Integer Bug: %d" totalIB
  log "  Mishandled Exception: %d" totalME
  log "  Multiple Send: %d" totalMS
  log "  Reentrancy: %d" totalRE
  log "  Suicidal Contract: %d" totalSC
  log "  Transaction Origin Use: %d" totalTO
  log "  Freezing Ether: %d" totalFE
  log "  Requirement Violation: %d" totalRV

let getTestCaseCount () =
  totalTC

(*** Record of paths and bugs ***)

let private updateBugCountAux (bugClass, _, _) =
  match bugClass with
  | BugClass.AssertionFailure -> totalAF <- totalAF + 1
  | BugClass.ArbitraryWrite -> totalAW <- totalAW + 1
  | BugClass.BlockstateDependency -> totalBD <- totalBD + 1
  | BugClass.ControlHijack -> totalCH <- totalCH + 1
  | BugClass.EtherLeak -> totalEL <- totalEL + 1
  | BugClass.IntegerBug -> totalIB <- totalIB + 1
  | BugClass.MishandledException -> totalME <- totalME + 1
  | BugClass.MultipleSend -> totalMS <- totalMS + 1
  | BugClass.Reentrancy -> totalRE <- totalRE + 1
  | BugClass.SuicidalContract -> totalSC <- totalSC + 1
  | BugClass.TransactionOriginUse -> totalTO <- totalTO + 1
  | BugClass.RequirementViolation -> totalRV <- totalRV + 1
  | _ -> ()

let private updateBugCount bugSet =
  Set.iter updateBugCountAux bugSet

(*** Test case storing functions ***)

let printBugInfo bugSet =
  let iterator (bugClass, pc, txIdx) =
    log "Tx#%d found %s at %x" txIdx (BugClassHelper.toString bugClass) pc
  Set.iter iterator bugSet

let private decideBugTag bugSet =
  Set.map (fun (bugType, _, _) -> bugType) bugSet
  |> Set.map BugClassHelper.toTag
  |> String.concat "-"

let private dumpBug opt seed bugSet =
  printBugInfo bugSet
  updateBugCount bugSet
  let tag = decideBugTag bugSet
  let tc = Seed.concretize seed
  let tcStr = TestCase.toJson tc
  let tcName = sprintf "id-%05d-%s_%05d" totalBug tag (elapsedSec())
  let tcPath = System.IO.Path.Combine(bugDir, tcName)
  if opt.Verbosity >= 0 then
    log "\n[*] Save bug seed %s: %s" tcName (Seed.toString seed)
  System.IO.File.WriteAllText(tcPath, tcStr)
  totalBug <- totalBug + 1

let private dumpTestCase opt seed =
  let tc = Seed.concretize seed
  let tcStr = TestCase.toJson tc
  let tcName = sprintf "id-%05d_%05d" totalTC (elapsedSec())
  let tcPath = System.IO.Path.Combine(tcDir, tcName)
  if opt.Verbosity >= 1 then
    log "\n[*] Save new seed %s: %s" tcName (Seed.toString seed)
    // printfn "\n"
  System.IO.File.WriteAllText(tcPath, tcStr)
  totalTC <- totalTC + 1

let mutable uvEdgeSeedMap = new Dictionary<int, Seed * bool>()
let mutable DefPool = new Dictionary<string, Seed list>()
let mutable DefUsePool = new Dictionary<string, Seed list>()

// Note: 判断是否defPC存在，并且在这里更新是否存在距离更近的分支
let evalAndSaveDefTC opt seed pc sIdx =
  // printfn "[*] execute seed: %s" (Seed.toString seed)
  // Note: 如果这里出现了新的DefPC不再执行，避免死循环？
  let covGain, duGain, defGain, bugSet, uvEdges = Executor.getDefCoverage opt seed pc sIdx
  // Note: 照常保存存在漏洞和覆盖新分支的测试用例
  if Set.count bugSet > 0 then dumpBug opt seed bugSet
  if covGain then dumpTestCase opt seed
  if not covGain && duGain && opt.Verbosity >= 2 then
    log "[*] Internal new seed: %s" (Seed.toString seed)
  // Note: 更新是否存在更近距离的分支，并且根据交易id，删除之后无影响的交易
  for edge in uvEdges.Keys do
    let struct (distOfItem, idOfItem) = uvEdges.Item edge
    if distOfItem <> bigint.Zero then
      if uvEdgeSeedMap.ContainsKey edge then
        let edgeSeed = fst (uvEdgeSeedMap.Item edge)
        let dist = snd edgeSeed.EdgeDist
        if dist > distOfItem then
          uvEdgeSeedMap.Remove edge |> ignore
          let txs = seed.Transactions
          let newTxs = txs.[0..idOfItem-1]
          if newTxs.Length > 0 then 
            let newSeed = { seed with Transactions = newTxs; TXCursor = newTxs.Length-1 }
            uvEdgeSeedMap.Add (edge, (newSeed, false)) |> ignore
      else
        let txs = seed.Transactions
        let newTxs = txs.[0..idOfItem-1]
        if newTxs.Length > 0 then
          let newSeed = { seed with Transactions = newTxs; TXCursor = newTxs.Length-1 }
          uvEdgeSeedMap.Add (edge, (newSeed, false)) |> ignore
  defGain
 
// Note: 根据DefPCs保存测试用例，并且这里无需执行污点分析
let evalAndSave opt random seed = 
  // printfn "[*] execute seed: %s" (Seed.toString seed)
  let covGain, duGain, bugSet, uvEdges, defPCs, defUsePCs = Executor.getCoverage opt seed
  // Note: 照常保存存在漏洞和覆盖新分支的测试用例
  if Set.count bugSet > 0 then dumpBug opt seed bugSet
  if covGain then dumpTestCase opt seed
  if not covGain && duGain && opt.Verbosity >= 2 then
    log "[*] Internal new seed: %s" (Seed.toString seed)
  // Note: 更新是否存在更近距离的分支，并且根据交易id，删除之后无影响的交易
  let mutable cnt = 0
  for edge in uvEdges.Keys do
    let struct (distOfItem, idOfItem) = uvEdges.Item edge
    if distOfItem <> bigint.Zero then
      if uvEdgeSeedMap.ContainsKey edge then
        let edgeSeed = fst (uvEdgeSeedMap.Item edge)
        let dist = snd edgeSeed.EdgeDist
        if dist > distOfItem then
          cnt <- cnt + 1
          uvEdgeSeedMap.Remove edge |> ignore
          let txs = seed.Transactions
          let newTxs = txs.[0..idOfItem]
          if newTxs.Length > 0 then
            let newSeed = { seed with Transactions = newTxs; TXCursor = idOfItem; EdgeDist = (edge, distOfItem) }
            uvEdgeSeedMap.Add (edge, (newSeed, false)) |> ignore
      else
        cnt <- cnt + 1
        let txs = seed.Transactions
        let newTxs = txs.[0..idOfItem]
        if newTxs.Length > 0 then
          let newSeed = { seed with Transactions = newTxs; TXCursor = idOfItem; EdgeDist = (edge, distOfItem) }
          uvEdgeSeedMap.Add (edge, (newSeed, false)) |> ignore
  // Note: 更新DefPool，即StorageIndex对应的txID并进行最小化
  // printfn "Update DefPool"
  // printfn "[*] execute seed: %s" (Seed.toString seed)
  for defPC in defPCs.Keys do
    let struct(pc, sIdx) = defPC
    let txIdx = defPCs.Item defPC
    // printfn "txIdx = %d" txIdx
    let mutable id = 1
    let mutable txs = seed.Transactions
    let mutable newTxs = txs.[0..txIdx]
    let mutable updateSeed = { seed with Transactions = newTxs; TXCursor = newTxs.Length-1 }
    let str = "s" + sIdx.ToString()
    // printfn "[*] def-%s updateSeed: %s" str (Seed.toString updateSeed)
    // Note: 最小化
    if updateSeed.Transactions.Length > 1 then 
      while id < updateSeed.Transactions.Length do
        // Note: 删除对应id的交易，看是否还有对应的def pc出现
        txs <- updateSeed.Transactions 
        let endLen = updateSeed.Transactions.Length-1
        if id = 0 then 
          newTxs <- txs.[1..endLen]
        else if id = endLen then
          newTxs <- txs.[0..(endLen-1)]
        else
          newTxs <- Array.append txs.[0..(id-1)] txs.[(id+1)..endLen]
        let trySeed = { updateSeed with Transactions = newTxs; TXCursor = newTxs.Length-1 }
        let res = evalAndSaveDefTC opt trySeed pc sIdx
        if res then
          // Note: 删除不影响
          updateSeed <- trySeed
        id <- id + 1
      // Note: 最小化种子更新进池子里
      if defUsePCs.ContainsKey defPC then
        if DefUsePool.ContainsKey str then
          DefUsePool.[str] <- updateSeed :: DefUsePool.[str]
        else 
          let mutable seedList = List.empty
          seedList <- updateSeed :: seedList
          DefUsePool.Add (str, seedList)
      else
        if DefPool.ContainsKey str then
          DefPool.[str] <- updateSeed :: DefPool.[str]
        else 
          let mutable seedList = List.empty
          seedList <- updateSeed :: seedList
          DefPool.Add (str, seedList)
  // covGain || duGain || cnt > 0
  // for defUsePC in defUsePCs.Keys do
  //   let struct(_, sIdx) = defUsePC
  //   let txIdx = defUsePCs.Item defUsePC
  //   let txs = seed.Transactions
  //   let txs1 = txs.[0..(txIdx-1)]
  //   let txs2 = [| txs.[txIdx-1] |]
  //   let newTxs = Array.append txs1 txs2
  //   let str = "s" + sIdx.ToString()
  //   let defUseSeed = { seed with Transactions = newTxs }
  //   if DefUsePool.ContainsKey str then
  //     DefUsePool.[str] <- defUseSeed :: DefPool.[str]
  //   else 
  //     let mutable seedList = List.empty
  //     seedList <- defUseSeed :: seedList
  //     DefUsePool.Add (str, seedList)
  // printfn "Update DefPool Finish"
  //if random then 
  covGain || duGain
  //else
  //cnt > 0

// Note: 获得最近的种子，并执行污点分析更新突变信息
let dealTaintSeeds opt =
  let mutable taintSeeds = List.empty
  let mutable kSet = List.empty
  for k in uvEdgeSeedMap.Keys do
    if Executor.accumEdges.Contains k then 
      kSet <- k :: kSet
    else 
      let item = uvEdgeSeedMap.Item k
      let seed = fst item
      if not (uvEdgeSeedMap.Item k |> snd) then
        // let item = uvEdgeSeedMap.Item k
        // let seed = fst item
        let tc = Seed.concretize seed
        let _, _, _, taintsOfJumpis, _, _, _  = Executor.getTaintCoverage opt seed
        let edge = k
        // Note: 仅保留
        // let struct (distOfItem, idOfItem) = uvEdges.Item edge
        let idOfItem = seed.Transactions.Length
        let inst1 = (edge &&& 0xffff0000) >>> 16    
        // 处理一下污点信息
        let mutable newMutPos = List.empty
        let mutable stateInfo = List.empty
        if taintsOfJumpis.ContainsKey inst1 then 
          for s in taintsOfJumpis.Item inst1 do
            // 状态变量
            if s.StartsWith "s" then
              stateInfo <- s :: stateInfo 
            else 
              // 污点信息调整位置
              let arr = s.Split ":"
              let idx = System.Int32.Parse arr.[0]
              if idx <= idOfItem then 
                if arr.Length > 2 then
                  let src = bigint.Parse arr.[1]
                  let length = bigint.Parse arr.[2]
                  let offsets = tc.Txs.Item(idx-1).Offsets
                  for i in 1 .. offsets.Length - 1 do
                    let sign = if idx = 0 then bigint.Zero else bigint.Parse offsets.[0]
                    let brr = offsets.[i].Split ":"
                    if brr.Length >= 2 then 
                      let argSrc = bigint.Parse brr.[0]
                      let argLen = bigint.Parse brr.[1]
                      if argSrc <= src - sign && argSrc + argLen >= src - sign + length then
                        // 参数从1开始
                        let mutPos = idx.ToString() + ":" + i.ToString()
                        newMutPos <- mutPos :: newMutPos
                      else if arr.[1] = "value" then
                        // 如果是value,对应的是参数0
                        let mutPos = idx.ToString() + ":0"
                        newMutPos <- mutPos :: newMutPos
                      else
                        let mutPos = idx.ToString() + ":sender"
                        newMutPos <- mutPos :: newMutPos
          let newSeed = Seed.setNewMutInfo seed (List.toArray newMutPos) stateInfo 
          taintSeeds <- newSeed :: taintSeeds 
        else
          taintSeeds <- seed :: taintSeeds 
        uvEdgeSeedMap.[k] <- (seed, true)
  List.map (fun x -> uvEdgeSeedMap.Remove x) kSet |> ignore
  taintSeeds

let getDefSeedList state = 
  DefPool.Item state

let judgeUvEdgeSeed seed = 
  let edge = seed.EdgeDist |> fst
  let dist = seed.EdgeDist |> snd
  if Executor.accumEdges.Contains edge then
    false
  else
    if uvEdgeSeedMap.ContainsKey edge then
      let uvSeed = uvEdgeSeedMap.Item edge |> fst
      let uvDist = uvSeed.EdgeDist |> snd
      if dist > uvDist then
        false
      else
        true
    else
      false
