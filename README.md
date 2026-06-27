# CODA

**CODA** (Critical-path Optimization via Decoupled Approach) is the first open-source multi-FPGA partitioning and routing tool dedicated to **critical path delay optimization**.

## Overview

Existing multi-FPGA system (MFS) partitioners mainly optimize cut size or net delay, but the true determinant of a circuit's clock frequency is the **critical path delay**. CODA tackles this with a novel **two-stage framework**:

1. **Stage 1 — Resource-aware partitioning:** Reduces the I/O resource utilization of inter-FPGA interconnections.
2. **Stage 2 — Critical-path optimization:** Aggressively optimizes critical path delay to achieve low latency.

Evaluated on the **Titan23** benchmark suite, CODA achieves a significant reduction in critical path delay compared to state-of-the-art methods.

## Build

```bash
g++ -o CODA CODA.cpp -std=c++17
```

## Usage

```bash
./CODA <data_name>
```

Replace `<data_name>` with the name of your input benchmark.

## Input Files

For a benchmark named `<data_name>`, the following files are expected:

### 1. Hypergraph netlist
**Path:** `./dataset/titan23/<data_name>/<data_name>_stratixiv_arch_timing.hgr`

- The first line contains two integers: the number of nets `m` and the number of nodes `n` (node indices start from 1).
- Each of the following `m` lines describes one net. The **first** index is the net's **driver**; the remaining indices are its **sinks**. Each net has exactly one driver but may have multiple sinks.

### 2. Sequential node list
**Path:** `./dataset/titan23/<data_name>/<data_name>_stratixiv_arch_timing_ff.txt`

- Each line contains one node index, marking that node as a sequential (flip-flop) node.

### 3. FPGA architecture graph
**Path:** `./dataset/FPGA_Graph/`

- The first line contains two integers: the number of FPGAs `n` (FPGA indices start from 0) and the number of interconnections `m`.
- Each of the following `m` lines contains two integers, representing the two endpoint FPGAs of one interconnection.

> Note: The FPGA graph file is not exposed as a command-line argument; readers can adjust it directly in the source code as needed.

## Requirements

- A C++17-compatible compiler (e.g., `g++`)
