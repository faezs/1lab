{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-darwin" "aarch64-linux" ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import ./support/nix/haskell-packages.nix) ];
        };
        agda = pkgs.agda;
      in
      {
        packages.default = (import ./default.nix { inherit pkgs; }).src;
        devShells.default = pkgs.mkShell {
          buildInputs = [
            (import ./default.nix { inherit pkgs; inNixShell = true;})
            agda
            pkgs.haskell.compiler.ghc94
          ];
        };
      });
}
