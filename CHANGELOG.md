# Changelog

## v2.0.0 - unreleased

### Migration from v1

- The synchronous entry points `scru64::new()` and `scru64::new_string()` are
  renamed to `scru64::new_sync()` and `scru64::new_string_sync()`, respectively.
- The `async-io` and `tokio` features are replaced by the newly implemented
  asynchronous entry points, `scru64::new()` and `scru64::new_string()`. Replace
  the old functions as follows:
  - `scru64::async_io::new()` -> `scru64::new()`
  - `scru64::async_io::new_string()` -> `scru64::new_string()`
  - `scru64::tokio::new()` -> `scru64::new()`
  - `scru64::tokio::new_string()` -> `scru64::new_string()`
- `scru64::gen` (alias to `scru64::generator`) is removed.

### Removed

- Deprecated aliases: `new()`, `new_string()`, and `gen`
- `async-io` and `tokio` features

### Added

- `new()` and `new_string()` as default asynchronous entry points

## v1.1.1 - 2024-09-11

### Fixed

- Memory leak issue of `generator::counter_mode::DefaultCounterMode`

## v1.1.0 - 2024-09-09

### Changed

- Names of primary functions from `new()` and `new_string()` to `new_sync()` and
  `new_string_sync()`, respectively
  - Leaving old names as aliases for backward compatibility

### Added

- `async-io` feature (`async_io::new()` and `async_io::new_string()`) to support
  `async-std` and `smol`

### Removed

- `new_with()`, `new_string_with()`, and `unstable` feature

## v1.0.3 - 2024-08-30

### Added

- `new_with()` and `new_string_with()` (via `unstable` crate feature) as
  undocumented experimental functions that may be removed or changed between
  minor releases

### Maintenance

- Separate test case testing env var-related functionality in a safe manner
- Code and document refactoring
- Test case cleaning

## v1.0.2 - 2024-08-29

### Fixed

- "Available on crate features ... only" labels in the document

## v1.0.1 - 2024-08-17

### Changed

- Name of `gen` module to `generator` to avoid forthcoming `gen` keyword
  - `gen` remains as an alias to `generator` for backward compatibility

## v1.0.0 - 2023-09-28

- Initial stable release
