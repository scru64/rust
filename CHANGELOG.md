# Changelog

## Unreleased

### Changed

- Parameters of `new_with()` and `new_string_with()` to allow callers to decide
  polling intervals

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
