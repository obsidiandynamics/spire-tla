`spire-tla`
===
TLA⁺ specifications of the **Spire** single-value consensus algorithm and the **Spanning Privilege** (SP) multi-value consensus algorithm. A pre-print of Spire and SP is available on IEEE's [TechRxiv](https://www.techrxiv.org/articles/preprint/Spire_A_Cooperative_Phase-Symmetric_Solution_to_Distributed_Consensus/13531136).

## Modules
|Module                |Description                          |
|:---------------------|:------------------------------------|
|`Spire.tla`           |Specification of the Spire algorithm.|
|`SpireSafe.tla`       |Bounded model checking of Spire's safety property.|
|`SpireLive.tla`       |Bounded model checking of Spire's liveness property.|
|`SpireTlaps.tla`      |Machine-verifiable proof of Spire's safety.|
|`SP.tla`              |Specification of the Spanning Privilege (SP) algorithm.|
|`SPSafe.tla`          |Bounded model checking of SP's safety.|

## Running
### Spire exhaustive correctness check
```sh
make check
```

### Spire random simulation
```sh
make sim
```

### Spire liveness check
```sh
make faircheck
```

### SP exhaustive correctness check
```sh
make multicheck
```

### Generate TLA⁺ PDF documents
```sh
make pdf
```