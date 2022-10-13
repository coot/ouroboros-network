# Contributing to Ouroboros-Network

## Coverage Reports

### Generating Coverage Reports

A haskell.nix project with coverage enabled for all project packages is exposed under the `coveredProject` attribute of `default.nix`:

```
nix-build default.nix -A coveredProject
```

A coverage report for the entire project can be generated and viewed with:

```
nix-build default.nix -A coveredProject.projectCoverageReport
xdg-open ./result/share/hpc/vanilla/html/index.html
```

Coverage reports for each individual package can be generated with:

```
nix-build default.nix -A coveredProject.hsPkgs.$pkg.coverageReport
xdg-open ./result/share/hpc/vanilla/html/index.html
```

Although individual package reports are also available in the entire project coverage report.

### Debugging Coverage Reports

The Nix derivation used to generate coverage reports can be debugged with:

```
nix-shell default.nix -A coveredProject.projectCoverageReport
OR nix-shell default.nix -A coveredProject.hsPkgs.$pkg.coverageReport
cd $(mktemp -d)
out=$(pwd) genericBuild
```

Build logs are written to stdout and artifacts written to the current directory.

## Releasing packages to CHaP

When new versions of the packages are released, they should be included in [CHaP](https://github.com/input-output-hk/cardano-haskell-packages).
See the CHaP README for [instructions](https://github.com/input-output-hk/cardano-haskell-packages#-from-github).

## Updating dependencies

Our Haskell packages come from two package repositories:
- Hackage
- [CHaP](https://github.com/input-output-hk/cardano-haskell-packages) (which is essentially another Hackage)

The "index state" of each repository is pinned to a particular time in
`cabal.project`.  This tells Cabal to treat the repository "as if" it was
the specified time, ensuring reproducibility.  If you want to use a package
version from repository X which was added after the pinned index state
time, you need to bump the index state for X.  This is not a big deal,
since all it does is change what packages `cabal` considers to be available
when doing solving, but it will change what package versions cabal picks
for the plan, and so will likely result in significant recompilation, and
potentially some breakage.  That typically just means that we need to fix
the breakage (and add a lower-bound on the problematic package), or add an
upper-bound on the problematic package.

Note that `cabal` itself keeps track of what index states it knows about, so
when you bump the pinned index state you may need call `cabal update` in
order for `cabal` to be happy.

The Nix code which builds our packages also cares about the index state.
This is represented by inputs managed by `niv`:
You can update these by running:
- `niv update hackage.nix` for Hackage
- `niv update cardano-haskell-packages` for CHaP

If you fail to do this you may get an error like this from Nix:
```
error: Unknown index-state 2021-08-08T00:00:00Z, the latest index-state I know about is 2021-08-06T00:00:00Z. You may need to update to a newer hackage.nix.
```

### Use of `source-repository-package`s

We *can* use Cabal's `source-repository-package` mechanism to pull in
un-released package versions. However, we should try and avoid this.  In
particular, we should not release our packages to CHaP while we depend on a
`source-repository-package`.

If we are stuck in a situation where we need a long-running fork of a
package, we should release it to CHaP instead (see the
https://github.com/input-output-hk/cardano-haskell-packages[CHaP README]
for more).

If you do add a `source-repository-package`, you need to provide a
`--sha256` comment in `cabal.project` so that Nix knows the hash of the
content.
