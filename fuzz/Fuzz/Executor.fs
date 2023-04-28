module Smartian.Executor

open System.IO
open System.Collections.Generic
open Nethermind.Dirichlet.Numerics
open Nethermind.Core.Test.Builders
open Nethermind.Core.Specs
open Nethermind.Evm
open Nethermind.Evm.Test
open Nethermind.Evm.Tracing
open Nethermind.Logging
open Nethermind.Store
open Config
open BytesUtils
open Options

type Env = {
  State : StateProvider
  SpecProvider: MainNetSpecProvider
  VM : VirtualMachine
  TxProcessor : TransactionProcessor
}

type Feedback = {
  CovGain : bool
  DUGain : bool
  DefGain : bool
  // PC, Op, Oprnd1, Oprnd2.
  CmpList : (uint64 * string * bigint * bigint) list
  // Bug class, Bug PC, Triggerring TX index.
  BugSet : Set<(BugClass * int * int)>
  TaintsOfJumpis : Dictionary<int, HashSet<string>>
  UnVisitedEdges : Dictionary<int, struct(bigint * int)>
  // Def PC * Storage Index
  DefPCs : Dictionary<struct(int * UInt256), int>
  DefUsePCs : Dictionary<struct(int * UInt256), int>
}

// Set of edge hashes.
let mutable accumEdges = SortedSet<int>()
// Set of program counters.
let mutable accumInstrs = SortedSet<int>()
// Set of (Def PC * Use PC * Storage Index)
let mutable accumDUChains = SortedSet<struct(int * int * UInt256)>()
// Set of (BugClass * PC)
let mutable accumBugs = Set.empty
// Set of (Def PC * Storage Index)
let mutable accumDefPCs = SortedSet<struct(int * UInt256)>()
// Dictionary of (Def PC * Storage Index)
let mutable dictOfDefPCs = new Dictionary<struct(int * UInt256), int>()
// Dictionary of (Def PC * Storage Index)
let mutable dictOfDefUsePCs = new Dictionary<struct(int * UInt256), int>()
// SortedSet of 
let mutable setOfDefPCs = SortedSet<struct(int * UInt256)>()

let mutable deployFailCount = 0

let mutable receivedEther = false
let mutable useDelegateCall = false
let mutable canSendEther = false

let mutable private targCode = [||]
let mutable private smartianAgentCode = [||]
let mutable private sFuzzAgentCode = [||]
// let mutable private functionsOrder = new Dictionary<string, int>()
// let mutable private offset = 1

let initialize targetPath =
  targCode <- File.ReadAllText(targetPath) |> hexStrToBytes
  let srcDir = Directory.GetParent(__SOURCE_DIRECTORY__).FullName
  let smartianAgentPath = Path.Join(srcDir, "Agent/AttackerContract.bin")
  smartianAgentCode <- File.ReadAllText(smartianAgentPath) |> hexStrToBytes
  let sFuzzAgentPath = Path.Join(srcDir, "Agent/SFuzzContract.bin")
  sFuzzAgentCode <- File.ReadAllText(sFuzzAgentPath) |> hexStrToBytes

let private initTestingEnv () =
  let logger = LimboLogs.Instance
  let codeDb = new StateDb()
  let stateDb = new StateDb()
  let state = StateProvider(stateDb, codeDb, logger)
  let storage = StorageProvider(stateDb, state, logger)
  let spec = MainNetSpecProvider.Instance
  let blockHash = TestBlockhashProvider()
  let vm = VirtualMachine(state, storage, blockHash, spec, logger)
  let processor = TransactionProcessor(spec, state, storage, vm, logger)
  state.Commit(spec.GenesisSpec)
  { State = state
    SpecProvider = spec
    VM = vm
    TxProcessor = processor }

let private runTx env from ``to`` code reqAddr value data timestamp blocknum txID =
  let processor = env.TxProcessor
  let tracer = CallOutputTracer()
  let block = Build.A.Block.WithTimestamp(UInt256(timestamp: int64))
                           .WithNumber(blocknum)
                           .WithGasLimit(BLOCK_GASLIMIT)
                           .WithBeneficiary(Address.MINER)
                           .TestObject
  let tx = Nethermind.Core.Transaction(SenderAddress = from,
                                       To = ``to``,
                                       Init = code,
                                       DeployAddress = reqAddr,
                                       Value = value,
                                       Data = data,
                                       GasLimit = TX_GASLIMIT,
                                       GasPrice = UInt256 (TX_GASPRICE: int64))
  env.VM.DefPCs.Clear()
  env.VM.DefUsePCs.Clear()
  env.VM.txID <- txID
  processor.Execute(tx, block.Header, tracer)
  tracer.StatusCode

let private deploy env deployer addr code value data timestamp blocknum =
  let code = Array.append code data
  let status = runTx env deployer null code addr value [| |] timestamp blocknum 0
  if status <> StatusCode.Success then deployFailCount <- deployFailCount + 1

let private setupAgent env deployer addr agentCode =
  let timestamp = DEFAULT_TIMESTAMP
  let blocknum = DEFAULT_BLOCKNUM
  deploy env deployer addr agentCode (UInt256 0L) [||] timestamp blocknum

let private setupEntity env tc entity =
  let state = env.State
  let vm = env.VM
  let specProvider = env.SpecProvider
  let targDeployer = tc.TargetDeployer
  let deployTx = tc.DeployTx
  let spec = specProvider.GetSpec(deployTx.Blocknum)
  match entity.Agent with
  | NoAgent ->
    state.CreateAccount(entity.Account, &entity.Balance)
    if targDeployer <> entity.Account then vm.RegisterUser(entity.Account)
  | SFuzzAgent contAddr ->
    let zero = UInt256(0I)
    state.CreateAccount(entity.Account, &zero)
    setupAgent env entity.Account contAddr sFuzzAgentCode
    state.AddToBalance(contAddr, &entity.Balance, spec)
    // sFuzz doesn't distinguish deployer and user.
  | SmartianAgent contAddr ->
    let zero = UInt256(0I)
    state.CreateAccount(entity.Account, &zero)
    setupAgent env entity.Account contAddr smartianAgentCode
    state.AddToBalance(contAddr, &entity.Balance, spec)
    if targDeployer <> contAddr then vm.RegisterUser(contAddr)

let private setupTarget env deployer addr tx =
  let vm = env.VM
  let value = tx.Value
  let data = tx.Data
  let timestamp = tx.Timestamp
  let blocknum = tx.Blocknum
  vm.IsDeployingTarget <- true
  deploy env deployer addr targCode value data timestamp blocknum
  vm.IsDeployingTarget <- false
  vm.TargetContractAddr <- addr
  vm.TargetOwnerAddr <- deployer

let private sendTx env covFlag hadDepTx isRedirect tx txID =
  let vm = env.VM
  vm.ResetPerTx()
  vm.HadDeployerTx <- hadDepTx
  vm.IsRedirected <- isRedirect
  runTx env tx.From tx.To null null tx.Value tx.Data tx.Timestamp tx.Blocknum txID
  |> ignore
  // Note: 在这更新是否存在新的Def PC
  let (curDefPCs : SortedSet<struct(int * UInt256)>) = vm.DefPCs
  setOfDefPCs.UnionWith(curDefPCs)
  curDefPCs.ExceptWith(accumDefPCs)
  if curDefPCs.Count <> 0 then
    for defPC in curDefPCs do
      dictOfDefPCs.Add (defPC, txID)
  let (curDefUsePCs : SortedSet<struct(int * UInt256)>) = vm.DefUsePCs
  curDefUsePCs.IntersectWith(curDefPCs)
  if curDefUsePCs.Count <> 0 then
    for defUsePC in curDefUsePCs do
      dictOfDefUsePCs.Add (defUsePC, txID)
  accumDefPCs.UnionWith(curDefPCs)
  if covFlag then
    accumEdges.UnionWith(vm.VisitedEdgeSet)
    accumInstrs.UnionWith(vm.VisitedInstrs)
    accumDUChains.UnionWith(vm.DefUseChainSet)
    accumBugs <- Set.ofSeq vm.BugSet
                 |> Set.map (fun struct (bugClass, pc) -> bugClass, pc)
                 |> Set.union accumBugs

// Check ether gain of users only if there was no previous deployer TX, because
// such TX can transfer the ownership to other users. Also, we check against
// both the initial balance and (immediate) previous balance to make sure that
// an attacker is actively, not passively, gaining ether.
let private checkEtherLeak (env: Env) sender hadDepTx initBal prevBal accBugs =
  let bug = (BugClass.EtherLeak, env.VM.BugOracle.LastEtherSendPC)
  if Set.contains bug accumBugs || hadDepTx then accBugs
  elif env.State.GetBalance(sender) <= initBal then accBugs
  elif env.State.GetBalance(sender) <= prevBal then accBugs
  else accumBugs <- Set.add bug accumBugs
       Set.add bug accBugs

let private processTx env tc covFlag (accNewBugs, hadDepTx) i (tx:TXData) =
  // Since we removed the foremost deploying transaction, should +1 to the index.
  let i = i + 1
  let sender = tx.From
  let isDepTx = (sender = tc.TargetDeployer)
  let hadDepTx = hadDepTx || isDepTx
  let initBalance, isRedirect =
    match List.tryFind (fun e -> Entity.getSender e = sender) tc.Entities with
    | Some entity -> (entity.Balance, Entity.isTXRedirected tx.To entity)
    | None -> failwithf "Invalid sender: %s" (Address.toStr sender)
  let prevBalance = env.State.GetBalance(sender)
  let prevBugs = accumBugs
  sendTx env covFlag hadDepTx isRedirect tx i
  let accNewBugs = Set.difference accumBugs prevBugs
                   |> checkEtherLeak env sender hadDepTx initBalance prevBalance
                   |> Set.map (fun (bug, pc) -> (bug, pc, i))
                   |> Set.union accNewBugs
  (accNewBugs, hadDepTx)

let private filterBugs checkOptional useOthersOracle bugs =
  let shouldSkip (bug, pc, ith) =
    if not checkOptional && BugClassHelper.isOptional bug then true
    elif not useOthersOracle && BugClassHelper.isFromOtherTools bug then true
    else false
  Set.filter (not << shouldSkip) bugs

/// Execute a seed (= transaction list) on EVM and return feedback.
let execute tc covFlag traceDU traceTaint checkOptional useOthersOracle =
  let env = initTestingEnv ()
  List.iter (setupEntity env tc) tc.Entities
  setupTarget env tc.TargetDeployer tc.TargetContract tc.DeployTx
  env.VM.TraceDU <- traceDU
  env.VM.TraceTaint <- traceTaint
  // Note: 记录新发现的Def PC以及对应的交易ID
  dictOfDefPCs <- new Dictionary<struct(int * UInt256), int>()
  dictOfDefUsePCs <- new Dictionary<struct(int * UInt256), int>()
  let oldEdgeCount = accumEdges.Count
  let oldDUChainCount = accumDUChains.Count
  let bugs = List.foldi (processTx env tc covFlag) (Set.empty, false) tc.Txs
             |> fst |> filterBugs checkOptional useOthersOracle
  let (taintsOfJumpis: Dictionary<int, HashSet<string>>) = env.VM.taintsOfJumpis
  let (uvEdges: Dictionary<int, struct(bigint * int)>) = env.VM.UnVisitedEdges
  // for k in uvEdges.Keys do
    //if accumEdges.Contains k then 
      //uvEdges.Remove k |> ignore
  let covGain = accumEdges.Count > oldEdgeCount
  let duGain = accumDUChains.Count > oldDUChainCount
  let defPCs = dictOfDefPCs
  let defUsePCs = dictOfDefUsePCs
  let conv struct (pc, op, oprnd1, oprnd2) = (uint64 pc, op, oprnd1, oprnd2)
  let cmpList = List.map conv (List.ofSeq env.VM.CmpList)
  let contractBalance = env.State.GetBalance(Address.TARG_CONTRACT)
  receivedEther <- receivedEther || contractBalance > (UInt256 0L)
  useDelegateCall <- useDelegateCall || env.VM.BugOracle.UseDelegateCall
  canSendEther <- canSendEther || env.VM.BugOracle.SendEtherIndependently
  { CovGain = covGain
    DUGain = duGain
    DefGain = false
    CmpList = cmpList
    BugSet = bugs
    TaintsOfJumpis = taintsOfJumpis
    UnVisitedEdges = uvEdges
    DefPCs = defPCs
    DefUsePCs = defUsePCs }

/// Execute a seed (= transaction list) on EVM and return feedback.
let executeDef tc covFlag traceDU traceTaint checkOptional useOthersOracle pc sIdx =
  let env = initTestingEnv ()
  List.iter (setupEntity env tc) tc.Entities
  setupTarget env tc.TargetDeployer tc.TargetContract tc.DeployTx
  env.VM.TraceDU <- traceDU
  env.VM.TraceTaint <- traceTaint
  // Note: 记录新发现的Def PC以及对应的交易ID
  dictOfDefPCs <- new Dictionary<struct(int * UInt256), int>()
  dictOfDefUsePCs <- new Dictionary<struct(int * UInt256), int>()
  setOfDefPCs <- new SortedSet<struct(int * UInt256)>()
  let oldEdgeCount = accumEdges.Count
  let oldDUChainCount = accumDUChains.Count
  let bugs = List.foldi (processTx env tc covFlag) (Set.empty, false) tc.Txs
             |> fst |> filterBugs checkOptional useOthersOracle
  let (taintsOfJumpis: Dictionary<int, HashSet<string>>) = env.VM.taintsOfJumpis
  let (uvEdges: Dictionary<int, struct(bigint * int)>) = env.VM.UnVisitedEdges
  // for k in uvEdges.Keys do
  //   if accumEdges.Contains k then 
  //     uvEdges.Remove k |> ignore
  let covGain = accumEdges.Count > oldEdgeCount
  let duGain = accumDUChains.Count > oldDUChainCount
  let defPCs = dictOfDefPCs
  let defUsePCs = dictOfDefUsePCs
  let defGain = setOfDefPCs.Contains (pc, sIdx)
  let conv struct (pc, op, oprnd1, oprnd2) = (uint64 pc, op, oprnd1, oprnd2)
  let cmpList = List.map conv (List.ofSeq env.VM.CmpList)
  let contractBalance = env.State.GetBalance(Address.TARG_CONTRACT)
  receivedEther <- receivedEther || contractBalance > (UInt256 0L)
  useDelegateCall <- useDelegateCall || env.VM.BugOracle.UseDelegateCall
  canSendEther <- canSendEther || env.VM.BugOracle.SendEtherIndependently
  { CovGain = covGain
    DUGain = duGain
    DefGain = defGain
    CmpList = cmpList
    BugSet = bugs
    TaintsOfJumpis = taintsOfJumpis
    UnVisitedEdges = uvEdges
    DefPCs = defPCs
    DefUsePCs = defUsePCs }

(*** Statistics ***)

let mutable totalExecutions = 0
let mutable phaseExecutions = 0

let getTotalExecutions () = totalExecutions
let getPhaseExecutions () = phaseExecutions
let resetPhaseExecutions () = phaseExecutions <- 0

(*** Resource scheduling ***)

let mutable allowedExecutions = 0
let allocateResource n = allowedExecutions <- n
let isExhausted () = allowedExecutions <= 0
let incrExecutionCount () =
  allowedExecutions <- allowedExecutions - 1
  totalExecutions <- totalExecutions + 1
  phaseExecutions <- phaseExecutions + 1

let private parseBranchInfo tryVal cmp =
  let addr, opStr, (oprnd1: bigint), (oprnd2: bigint)= cmp
  let dist = oprnd1 - oprnd2
  let brType =
    match opStr with
    | "==" -> Equality
    | "!=" -> Equality
    | ">=s" -> SignedSize
    | ">s" -> SignedSize
    | "<=s" -> SignedSize
    | "<s" -> SignedSize
    | ">=u" -> UnsignedSize
    | ">u" -> UnsignedSize
    | "<=u" -> UnsignedSize
    | "<u" -> UnsignedSize
    | _ -> failwithf "Unimplemented operation string : %s" opStr
  { InstAddr = addr
    BrType = brType
    TryVal = tryVal
    OpSize = 32
    Oprnd1 = oprnd1
    Oprnd2 = oprnd2
    Distance = dist }

let rec private parseBranchInfoAtAux tryVal targPoint accMap cmpList =
  match cmpList with
  | [] -> None
  | headCmp :: tailCmpList ->
    let addr, opStr, oprnd1, oprnd2 = headCmp
    // Caution : we count first visit as '1', instead of '0'.
    let count = if Map.containsKey addr accMap then Map.find addr accMap else 1
    if (addr, count) = (targPoint.Addr, targPoint.Idx) then
      Some (parseBranchInfo tryVal headCmp)
    else
      let newMap = Map.add addr (count + 1) accMap
      parseBranchInfoAtAux tryVal targPoint newMap tailCmpList

let private parseBranchInfoAt tryVal targPoint cmpList =
  parseBranchInfoAtAux tryVal targPoint Map.empty cmpList

let private parseBranchTrace tryVal cmpList =
  List.map (parseBranchInfo tryVal) cmpList

(*** Tracer execute functions ***)

let private runEVM opt seed covFlag traceTaint =
  incrExecutionCount ()
  // printfn "\n[*] execute seed: %s" (Seed.toString seed)
  let tc = Seed.concretize seed
  // printfn "[*] execute testcase: %s" (TestCase.toJson tc)
  execute tc covFlag opt.DynamicDFA traceTaint opt.CheckOptionalBugs opt.UseOthersOracle

let private runEVMDef opt seed covFlag traceTaint pc sIdx =
  incrExecutionCount ()
  // printfn "\n[*] execute seed: %s" (Seed.toString seed)
  let tc = Seed.concretize seed
  // printfn "[*] execute testcase: %s" (TestCase.toJson tc)
  executeDef tc covFlag opt.DynamicDFA traceTaint opt.CheckOptionalBugs opt.UseOthersOracle pc sIdx

(*** Top-level executor functions ***)

let getCoverage opt seed =
  let f = runEVM opt seed true false
  f.CovGain, f.DUGain, f.BugSet, f.UnVisitedEdges, f.DefPCs, f.DefUsePCs

let getDefCoverage opt seed pc sIdx =
  let f = runEVMDef opt seed true false pc sIdx
  f.CovGain, f.DUGain, f.DefGain, f.BugSet, f.UnVisitedEdges

let getTaintCoverage opt seed =
  let f = runEVM opt seed true true
  f.CovGain, f.DUGain, f.BugSet, f.TaintsOfJumpis, f.UnVisitedEdges, f.DefPCs, f.DefUsePCs

let getBranchTrace opt seed tryVal =
  let f = runEVM opt seed false false
  parseBranchTrace tryVal f.CmpList

let getBranchInfoAt opt seed tryVal targPoint =
  let f = runEVM opt seed false false
  parseBranchInfoAt tryVal targPoint f.CmpList
