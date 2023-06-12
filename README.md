# SeqFuzz
A Guided Mutation Strategy for Smart Contract Fuzzing

## Introduction
SeqFuzz is a guided fuzzer for Ethereum smart contracts, which equips a guided mutation strategy. We implement SeqFuzz using the guided mutation strategy for smart contract fuzzing. Note that our work focuses on the guided mutation to satisfy complex constraints, so we draw on existing works for the definition of vulnerability detection and the preprocessing of the smart contracts bytecode. By default, SeqFuzz supports ten oracles inspired by Smartian. For the preprocessing of smart contracts, we use the framework of Smartian. It utilizes B2R2 as the front-end to parse and disassemble EVM bytecode, and uses Nethermind EVM to deploy smart contracts and emulate transactions using dynamic instrumentation. We use ABI to set the parameter types and the length of the corresponding byte stream.

## Dataset
The dataset for evaluation can be found in ```dataset``` directory.
1 corresponds to the D1 dataset in the paper, where the contracts are all CVE contracts.
2 corresponds to the D2 dataset in the paper, where the contracts are all contracts on Etherscan.

## Run
For contracts that provide ABI and bytecode, we can run them directly.
```$ dotnet build/Smartian.dll fuzz -p <bytecode file> -a <abi file> -t <time limit> -o <output dir>```

For contracts that provide source code, we first compile to get the ABI and bytecode.
If the master contract name is not provided, we execute ```writh.sh``` selection of abi and bytecode.
Then, run
```$ dotnet build/Smartian.dll fuzz -p <bytecode file> -a <abi file> -t <time limit> -o <output dir>```

