{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    hasktorch'.url = "github:hasktorch/hasktorch";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, hasktorch', flake-utils }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-darwin" "aarch64-linux" ] (system:
      let
        hasktorch = hasktorch';
        pkgs = import nixpkgs {
          inherit system;
          #overlays = [ hasktorch.overlays.default ];
        };
        agdaWithLibs = pkgs.agda.withPackages (p: [ p.standard-library ]);
        hasktorchPkgs = hasktorch.packages;
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithLibs
            pkgs.haskell.compiler.ghc94
            hasktorchPkgs.hasktorch
            pkgs.python3Packages.torch
          ];
          shellHook = ''
            export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib:${hasktorchPkgs.libtorch}/lib:$LD_LIBRARY_PATH
          '';
        };
      });
}
