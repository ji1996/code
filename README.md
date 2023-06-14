# SeqFuzz
A Guided Mutation Strategy for Smart Contract Fuzzing

## Introduction
SeqFuzz is a guided fuzzer for Ethereum smart contracts, which equips a guided mutation strategy. We implement SeqFuzz using the guided mutation strategy for smart contract fuzzing. Note that our work focuses on guided mutation to satisfy complex constraints, so we draw on existing works for the definition of vulnerability detection and the preprocessing of the smart contracts bytecode. By default, SeqFuzz supports ten oracles inspired by Smartian. For the preprocessing of smart contracts, we use the framework of Smartian. It utilizes B2R2 as the front-end to parse and disassemble EVM bytecode, and uses Nethermind EVM to deploy smart contracts and emulate transactions using dynamic instrumentation. We use ABI to set the parameter types and the length of the corresponding byte stream.

## Dataset
The dataset for evaluation can be found in ```dataset``` directory.
1 corresponds to the D1 dataset in the paper, where the contracts are all CVE contracts.
2 corresponds to the D2 dataset in the paper, where the contracts are all contracts on Etherscan.

## Results
The experimental results in the paper can be found in ```Results```.

## Installation
The tool is written in F#, so you have to install .NET to run. Installation step differs for each Linux distribution, please install net5.0. 

## Run
For contracts that provide ABI and bytecode, we can run them directly.
```
$ bin/testFuzz <bytecode file> <abi file> <time limit> <output dir>
```

We first compile for contracts that provide source code to get the ABI and bytecode.
If the master contract name is not provided, execute ```writh.sh``` selection of abi and bytecode.
Then, run
```
$ bin/testFuzz <bytecode file> <abi file> <time limit> <output dir>
```

