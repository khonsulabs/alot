<!-- markdownlint-disable MD024 -->
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## v0.3.0 (2023-07-25)

### Added

- `OrderedLots::remove_by_index()` removes a value by its index.
- `OrderedLots::index_of_id()` returns the index of a contained LotId.
- `OrderedLots::id()` returns the LotId for a given index.
- `OrderedLots::first()`/`first_mut()`/`last()`/`last_mut()` have been added to
  return the first and last elements in the collection.
- `OrderedLots::swap()` swaps the location of two values contained in the
  collection.

## v0.2.0 (2023-06-21)

### Breaking Changes

- `LotId::index`, `LotId::generation`, and `Generation` are now private.

### Added

- `LotId::to_bytes` and `LotId::from_bytes` are functions that encode and decode
  a `LotId` into a portable representation. This has been designed such that if
  two networked clients were applying identically ordered changes to their
  collections and exchanging `LotId`s, the byte representations would be
  compatible regardless of what CPU architecture generated the bytes.
- `ordered::Lots::pop`/`ordered::Lots::pop_entry` are new functions that remove
  the final item from the collection.
- `LotId` now implements `Ord`.

## v0.1.0 (2023-05-02)

Initial release.
