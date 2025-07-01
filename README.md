# RSL* Transpiler

This repository contains the source code for rslst, a partial transpiler for unfolding specifications using a specific subset of RSL*.

## Usage

The transpiler provides the following commands:

- Typecheck a specification:

```sh
rslst typecheck <specification-path>
```

- Typecheck and unfold a specification.

```sh
rslst unfold <specification-path>
```

The unfolded result will be written to X_unfolded.rsl, where X is the name of the input file.

## Build & Test

To build the project:

```sh
dotnet build
```

To run tests:

```sh
dotnet test
```

## Notes

> 🛠️ Console error formatting is inspired by [miette](https://github.com/zkat/miette)
