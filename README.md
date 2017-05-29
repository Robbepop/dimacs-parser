[![Build Status](https://travis-ci.org/Robbepop/dimacs-parser.svg?branch=master)](https://travis-ci.org/Robbepop/dimacs-parser)
[![Build status](https://ci.appveyor.com/api/projects/status/9nl84slw5xw17hd9/branch/master?svg=true)](https://ci.appveyor.com/project/Robbepop/dimacs-parser/branch/master)
[![Crates.io Version](https://img.shields.io/crates/v/dimacs.svg)](https://crates.io/crates/dimacs)
[![Doc.rs Badge](https://docs.rs/dimacs/badge.svg)](https://docs.rs/dimacs)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)

DIMACS Parser
=============

Utilities to parse files in DIMACS `.cnf` or `.sat` SAT format which is useful in participating in the DIMACS SAT solver competition.

Basically provides the following API:

```rust
fn parse_dimacs(input: &str) -> Result<Instance> { .. }
```
