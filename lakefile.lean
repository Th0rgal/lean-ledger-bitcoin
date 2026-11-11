import Lake
open Lake DSL

package «lean-ledger-bitcoin» where
  version := v!"0.1.0"

@[default_target]
lean_lib «Spec» where
  roots := #[`Spec]
  precompileModules := false

@[default_target]
lean_lib «InternalSpec» where
  roots := #[`InternalSpec]
  precompileModules := false

@[default_target]
lean_lib «BitcoinLedger» where
  roots := #[`BitcoinLedger]
  precompileModules := false

@[default_target]
lean_lib «Proofs» where
  roots := #[`Proofs]
  precompileModules := false

lean_lib «Tests» where
  roots := #[`Tests]
  precompileModules := false
