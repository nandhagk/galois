{
  description = "Galois: general, composable program analyses in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/c9fe7d12cd78d1adcd12dd15e24432dde5b155a0";
  inputs.argent.url = "github:nandhagk/argent/dcba5cc6cc8134ac521e177fbb97f9d59e4e1ea2";
  inputs.argent.inputs.nixpkgs.follows = "nixpkgs";

  outputs =
    { nixpkgs, argent, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      pkgsFor = system: import nixpkgs { inherit system; };
    in
    {
      devShells = nixpkgs.lib.genAttrs systems (system: {
        default = (import ./nix { pkgs = pkgsFor system; argent = argent.packages.${system}.default; }).devShell;
      });
      formatter = nixpkgs.lib.genAttrs systems (system: (pkgsFor system).nixfmt);
    };
}
