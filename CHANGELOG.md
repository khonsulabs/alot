<!-- markdownlint-disable MD024 -->
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## v0.2.0

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

## v0.1.0

Initial release.
