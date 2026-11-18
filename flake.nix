{
  description = "Galois: general, composable program analyses in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/c9fe7d12cd78d1adcd12dd15e24432dde5b155a0";
  inputs.argent.url = "github:nandhagk/argent/d3c0154de56a3a725d5e89a974c72237d2e6de08";
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
        session = (import ./nix { pkgs = pkgsFor system; argent = argent.packages.${system}.default; }).sessionShell;
      });
      formatter = nixpkgs.lib.genAttrs systems (system: (pkgsFor system).nixfmt);
    };
}
